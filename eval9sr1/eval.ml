open Syntax
open Value

(* interpreter with defunctionalized instructions : eval9s *)

let idc = []

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c9 : c -> s -> r -> t -> m -> v *)
let rec run_c9 c s r t m = match (c, s, r) with
    ([], v :: [], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, r, t), m) -> run_c9 c (v :: s) r t m
        end
      | Trail (h) -> h v TNil m
    end
  | ((i1, vs) :: c, (v :: s), r) ->
    run_i9 i1 vs c (v :: s) r t m

and run_i9 i vs c s r t m = match i with
    INum (n) -> run_c9 c (VNum (n) :: s) r t m
  | IAccess (n) -> run_c9 c (List.nth vs n :: s) r t m
  | IOp (op) ->
    begin match s with
        v0 :: v1 :: s ->
        begin match (v0, v1) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c9 c (VNum (n0 + n1) :: s) r t m
              | Minus -> run_c9 c (VNum (n0 - n1) :: s) r t m
              | Times -> run_c9 c (VNum (n0 * n1) :: s) r t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c9 c (VNum (n0 / n1) :: s) r t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                          ^ " are not numbers")
        end
      | _ -> failwith "stack error: op"
    end
  | IPushmark -> run_c9 c (VArgs ([]) :: s) r t m
  | IPush ->
    begin match s with v :: VArgs (v2s) :: s ->
        run_c9 c (VArgs (v :: v2s) :: s) r t m
      | _ -> failwith "stack error: IPush"
    end
  | IApply ->
    begin match s with
        v0 :: VArgs (v2s) :: s ->
        begin match v2s with
            [] -> run_c9 c (v0 :: s) r t m
          | v1 :: v2s ->
            begin match v0 with
                VFun (i, vs) -> run_i9 i vs [] (v1 :: VArgs (v2s) :: s) (VK ((IApply, vs) :: c) :: r) t m
              | VContS (c', s', r', t') ->
                run_c9 c' (v1 :: s') r' t' (MCons (((IApply, vs) :: c, VArgs (v2s) :: s, r, t), m))
              | VContC (c', s', r', t') ->
                (* let trail = fun v t m -> run_c9 ((IApply, vs) :: c) (v :: VArgs (v2s) :: s) r t m in *)
                let trail = fun v t m -> run_i9 IApply vs c (v :: VArgs (v2s) :: s) r t m in
                run_c9 c' (v1 :: s') r' (apnd t' (cons trail t)) m
                (* let trail = Hold ((IApply, vs) :: c, v0 :: VArgs (v2s) :: s, r) in
                run_c9 c' (v1 :: s') r' (apnd t' (cons trail t)) m *)
              | _ -> failwith (to_string v0
                              ^ " is not a function; it can not be applied.")
            end
        end
      | _ -> failwith "stack error: IApply"
      end
  (* | IAppTrail (v) ->
    run_c9 ((IApply, vs) :: c) (v :: VArgs (v2s) :: s) r t m *)
  | IReturn (i) ->
    begin match (s, r) with
        (v1 :: s', VK (c') :: r') -> run_i9 i (v1 :: vs) c' s' r' t m
      | _ -> failwith "stack error"
    end
  | IFun (i) ->
    begin match (c, s, r) with
        ((i', vs') :: c', VArgs (v1 :: v2s) :: s', r') when i' == IApply ->
        (* print_endline ("grab: " ^ Value.s_to_string s); *)
        run_i9 i (v1 :: vs) ((i', vs') :: c') (VArgs (v2s) :: s') r' t m (*Grab*)
      | _ -> (* Cur *)
        (* let vfun = VFun (fun _ s' (VK (c') :: r') t' m' ->
          begin match s' with
            v1 :: s' -> run_i9 i (v1 :: vs) c' s' r' t' m'
          | _ -> failwith "stack error"
          end) in *)
        run_c9 c (VFun (IReturn (i), vs) :: s) r t m
    end
  | IShift (i) ->
    run_i9 i (VContS (c, s, r, t) :: vs) [] [] [] TNil m
  | IControl (i) ->
    run_i9 i (VContC (c, s, r, t) :: vs) [] [] [] TNil m
  | IShift0 (i) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        run_i9 i (VContS (c, s, r, t) :: vs) c0 s0 r0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | IControl0 (i) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        run_i9 i (VContC (c, s, r, t) :: vs) c0 s0 r0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | IReset (i) ->
    run_i9 i vs [] [] [] TNil (MCons ((c, s, r, t), m))
  | ISeq (i0, i1) ->
    run_i9 i0 vs ((i1, vs) :: c) s r t m

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = ISeq (i0, i1)

(* f9 : e -> string list -> i *)
let rec f9 e xs = match e with
    Num (n) -> INum (n)
  | Var (x) -> IAccess (Env.offset x xs)
  | Op (e0, op, e1) -> f9 e1 xs >> f9 e0 xs >> IOp (op)
  | Fun (x, e) -> IFun (f9 e (x :: xs))
  | App (e0, e2s) ->
    f9s e2s xs >> f9 e0 xs >> IApply
  | Shift (x, e) -> IShift (f9 e (x :: xs))
  | Control (x, e) -> IControl (f9 e (x :: xs))
  | Shift0 (x, e) -> IShift0 (f9 e (x :: xs))
  | Control0 (x, e) -> IControl0 (f9 e (x :: xs))
  | Reset (e) -> IReset (f9 e xs)

(* f9s : e list -> string list -> i *)
and f9s e2s xs = match e2s with
    [] -> IPushmark
  | e :: e2s -> f9s e2s xs >> f9 e xs >> IPush

(* f : e -> v *)
let f expr = run_i9 (f9 expr []) [] idc [] [] TNil MNil
