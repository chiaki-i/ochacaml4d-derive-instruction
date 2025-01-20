open Syntax
open Value

(* linearize i; derived from eval9s2 *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c9 : c -> s -> t -> m -> v *)
let rec run_c9 c s t m = match (c, s) with
    ([], v :: []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c9 c (v :: s) t m
        end
      | Trail (h) -> h v TNil m
    end
  | (([], vs) :: c, s) -> run_c9 c s t m
  | ((INum (n) :: is, vs) :: c, s) ->
    run_c9 ((is, vs) :: c) (VNum (n) :: s) t m
  | ((IAccess (n) :: is, vs) :: c, s) ->
    run_c9 ((is, vs) :: c) (List.nth vs n :: s) t m
  | ((IOp (op) :: is, vs) :: c, s) ->
    begin match s with
        v0 :: v1 :: s ->
        begin match (v0, v1) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c9 ((is, vs) :: c) (VNum (n0 + n1) :: s) t m
              | Minus -> run_c9 ((is, vs) :: c) (VNum (n0 - n1) :: s) t m
              | Times -> run_c9 ((is, vs) :: c) (VNum (n0 * n1) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c9 ((is, vs) :: c) (VNum (n0 / n1) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                          ^ " are not numbers")
        end
      | _ -> failwith "stack error: op"
    end
  | ((IPushmark :: is, vs) :: c, s) ->
    run_c9 ((is, vs) :: c) (VArgs ([]) :: s) t m
  | ((IPush :: is, vs) :: c, s) ->
    begin match s with v :: VArgs (v2s) :: s ->
        run_c9 ((is, vs) :: c) (VArgs (v :: v2s) :: s) t m
      | _ -> failwith "stack error: IPush"
    end
  | ((IApply :: is, vs) :: c, s) ->
    begin match s with
      v0 :: VArgs ([]) :: s -> run_c9 ((is, vs) :: c) (v0 :: s) t m
    | VFun (f) :: VArgs (v1 :: v2s) :: s ->
      f (([IApply], vs) :: (is, vs) :: c) (v1 :: VArgs (v2s) :: s) t m
    | VContS (c', s', t') :: VArgs (v1 :: v2s) :: s ->
      run_c9 c' (v1 :: s') t'
             (MCons ((([IApply], vs) :: (is, vs) :: c, VArgs (v2s) :: s, t), m))
    | VContC (c', s', t') :: VArgs (v1 :: v2s) :: s ->
      run_c9 c' (v1 :: s')
             (apnd t' (cons (fun v t m ->
               run_c9 (([IApply], vs) :: (is, vs) :: c)
                      (v :: VArgs (v2s) :: s) t m) t)) m
    | v0 :: VArgs (v1 :: v2s) :: s ->
      failwith (to_string v0
                ^ " is not a function; it can not be applied.")
    | _ -> failwith "stack error: IApply"
    end
  | ((IFun (i) :: is, vs) :: c, s) ->
    begin match (c, s) with
        (*
        ((IApply, vs') :: c', VArgs (v1 :: v2s) :: s') -> (* Grab *)
          (* print_endline ("grab: " ^ Value.s_to_string s); *)
        run_i9 i (v1 :: vs) ((IApply, vs') :: c') (VArgs (v2s) :: s') t m
        *)
      | _ ->
        let vfun = VFun (fun c' s' t' m' ->
          begin match s' with
            v1 :: s' -> run_c9 ((i, v1 :: vs) :: c') s' t' m'
          | _ -> failwith "stack error"
          end) in
        run_c9 ((is, vs) :: c) (vfun :: s) t m
    end
  | ((IShift (i) :: is, vs) :: c, s) ->
    run_c9 ((i, VContS ((is, vs) :: c, s, t) :: vs) :: []) [] TNil m
  | ((IControl (i) :: is, vs) :: c, s) ->
    run_c9 ((i, VContC ((is, vs) :: c, s, t) :: vs) :: []) [] TNil m
  | ((IShift0 (i) :: is, vs) :: c, s) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_c9 ((i, VContS ((is, vs) :: c, s, t) :: vs) :: c0) s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | ((IControl0 (i) :: is, vs) :: c, s) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_c9 ((i, VContC ((is, vs) :: c, s, t) :: vs) :: c0) s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | ((IReset (i) :: is, vs) :: c, s) ->
    run_c9 ((i, vs) :: []) [] TNil (MCons (((is, vs) :: c, s, t), m))
  | _ -> failwith "run_c9: stack error"

(* f9 : e -> string list -> i *)
let rec f9 e xs = match e with
    Num (n) -> [INum (n)]
  | Var (x) -> [IAccess (Env.offset x xs)]
  | Op (e0, op, e1) -> f9 e1 xs @ f9 e0 xs @ [IOp (op)]
  | Fun (x, e) -> [IFun (f9 e (x :: xs))]
  | App (e0, e2s) -> f9s e2s xs @ f9 e0 xs @ [IApply]
  | Shift (x, e) -> [IShift (f9 e (x :: xs))]
  | Control (x, e) -> [IControl (f9 e (x :: xs))]
  | Shift0 (x, e) -> [IShift0 (f9 e (x :: xs))]
  | Control0 (x, e) -> [IControl0 (f9 e (x :: xs))]
  | Reset (e) -> [IReset (f9 e xs)]

(* f9s : e list -> string list -> i *)
and f9s e2s xs = match e2s with
    [] -> [IPushmark]
  | e :: e2s -> f9s e2s xs @ f9 e xs @ [IPush]

(* f : e -> v *)
let f expr = run_c9 ((f9 expr [], []) :: []) [] TNil MNil
