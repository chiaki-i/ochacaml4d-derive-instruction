open Syntax
open Value

(* interpreter with defunctionalized instructions : eval10sr *)

let idc = []

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c10 : c -> s -> r -> t -> m -> v *)
let rec run_c10 vs c s r t m = match (c, s, r) with
    ([], v :: [], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, r, t), m) -> run_c10 vs c (v :: s) r t m
        end
      | Trail (h) -> h v TNil m
    end
  | (INum (n) :: c, s, r) ->
    run_c10 vs c (VNum (n) :: s) r t m
  | (IAccess (n) :: c, s, r) ->
    run_c10 vs c (List.nth vs n :: s) r t m
  | (IOp (op) :: c, s, r) ->
    begin match s with
        v0 :: v1 :: s ->
        begin match (v0, v1) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c10 vs c (VNum (n0 + n1) :: s) r t m
              | Minus -> run_c10 vs c (VNum (n0 - n1) :: s) r t m
              | Times -> run_c10 vs c (VNum (n0 * n1) :: s) r t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c10 vs c (VNum (n0 / n1) :: s) r t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                          ^ " are not numbers")
        end
      | _ -> failwith "stack error: op"
    end
  | (IPushmark :: c, s, r) ->
    run_c10 vs c (VArgs ([]) :: s) r t m
  | (IPush :: c, s, r) ->
    begin match s with v :: VArgs (v2s) :: s ->
        run_c10 vs c (VArgs (v :: v2s) :: s) r t m
      | _ -> failwith "stack error: IPush"
    end
  | (IApply :: c, s, r) ->
    begin match s with
        v0 :: VArgs (v2s) :: s ->
        begin match v2s with
            [] -> run_c10 vs c (v0 :: s) r t m
          | v1 :: v2s ->
            begin match v0 with
                VFun (f) ->
                f [] (v1 :: VArgs (v2s) :: s) (VK (IApply :: c) :: r) t m
              | VContS (c', s', r', t') ->
                run_c10 vs c' (v1 :: s') r' t' (MCons ((IApply :: c, VArgs (v2s) :: s, r, t), m))
              | VContC (c', s', r', t') ->
                run_c10 vs c' (v1 :: s') r'
                  (apnd t' (cons (fun v t m -> run_c10 vs (IApply :: c) (v :: VArgs (v2s) :: s) r t m) t)) m
              | _ -> failwith (to_string v0
                              ^ " is not a function; it can not be applied.")
            end
        end
      | _ -> failwith "stack error: IApply"
      end
  | (IFun (i) :: c, s, r) ->
    begin match (c, s, r) with
        (i' :: c', VArgs (v1 :: v2s) :: s', r') when i' == IApply ->
        (* print_endline ("grab: " ^ Value.s_to_string s); *)
        run_c10 (v1 :: vs) (i :: i' :: c') (VArgs (v2s) :: s') r' t m (* Grab *)
      | _ ->
        let vfun = VFun (fun _ s' (VK (c') :: r') t' m' ->
          begin match s' with
            v1 :: s' -> run_c10 (v1 :: vs) (i :: c') s' r' t' m'
          | _ -> failwith "stack error"
          end) in
        run_c10 vs c (vfun :: s) r t m
    end
  | (IShift (i) :: c, s, r) ->
    run_c10 (VContS (c, s, r, t) :: vs) (i :: c) [] [] TNil m
  | (IControl (i) :: c, s, r) ->
    run_c10 (VContC (c, s, r, t) :: vs) (i :: c) [] [] TNil m
  | (IShift0 (i) :: c, s, r) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        run_c10 (VContS (c, s, r, t) :: vs) (i :: c0) s0 r0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | (IControl0 (i) :: c, s, r) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        run_c10 (VContC (c, s, r, t) :: vs) (i :: c0) s0 r0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | (IReset (i) :: c, s, r) ->
    run_c10 vs (i :: []) [] [] TNil (MCons ((c, s, r, t), m))

(* f10 : e -> string list -> i *)
(* f10 : e -> string list -> c *)
let rec f10 e xs = match e with
    Num (n) -> [INum (n)]
  | Var (x) -> [IAccess (Env.offset x xs)]
  | Op (e0, op, e1) ->
    (f10 e1 xs) @ (f10 e0 xs) @ [IOp (op)]
  | Fun (x, e) -> [IFun (f10 e (x :: xs))]
  | App (e0, e2s) ->
    (f10s e2s xs) @ (f10 e0 xs) @ [IApply]
  | Shift (x, e) -> [IShift (f10 e (x :: xs))]
  | Control (x, e) -> [IControl (f10 e (x :: xs))]
  | Shift0 (x, e) -> [IShift0 (f10 e (x :: xs))]
  | Control0 (x, e) -> [IControl0 (f10 e (x :: xs))]
  | Reset (e) -> [IReset (f10 e xs)]

(* f10s : e list -> string list -> i *)
and f10s e2s xs = match e2s with
    [] -> [IPushmark]
  | e :: e2s -> [f10s e2s xs] @ [f10 e xs] @ [IPush]

(* f : e -> v *)
let f expr = run_c10 [] (f10 expr []) [] [] TNil MNil