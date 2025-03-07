open Syntax
open Value

(* defintionalized continuations: eval10ds *)
(* derived from eval8ds *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

let idc = []

(* run_c10 : c -> s -> t -> m -> v *)
let rec run_c10 c s t m = match (c, s) with
    ([], v :: []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c10 c (v :: s) t m
        end
      | Trail (h) -> h v TNil m
    end
  | ((c', vs) :: c, v :: s) ->
    run_i10 c' vs c (v :: s) t m

(* run_c10 : i -> v list -> c -> s -> t -> m -> v *)
and run_i10 i vs c s t m = match (i, s) with
  | (INum (n), s) -> run_c10 c (VNum (n) :: s) t m
  | (IAccess (n), s) -> run_c10 c (List.nth vs n :: s) t m
  | (IOp (op), v0 :: v1 :: s) ->
    begin match (v0, v1) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c10 c (VNum (n0 + n1) :: s) t m
          | Minus -> run_c10 c (VNum (n0 - n1) :: s) t m
          | Times -> run_c10 c (VNum (n0 * n1) :: s) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c10 c (VNum (n0 / n1) :: s) t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                        ^ " are not numbers")
    end
  | (IPushmark, s) -> run_c10 c (VArgs ([]) :: s) t m
  | (IPush, v :: VArgs (v2s) :: s) -> run_c10 c (VArgs (v :: v2s) :: s) t m
  | (IFun (i), s) ->
    begin match (c, s) with
        ((i', vs') :: c', VArgs (v1 :: v2s) :: s') when i' == IApply -> (* Grab *)
        run_i10 i (v1 :: vs) ((i', vs') :: c') (VArgs (v2s) :: s') t m
      | _ ->
        run_c10 c (VFun (fun c' (v1 :: s') t' m' -> run_i10 i (v1 :: vs) c' s' t' m') :: s) t m
    end
  | (IApply, v0 :: VArgs (v2s) :: s) -> apply10s v0 v2s vs c s t m
  | (IShift (i), s) -> run_i10 i (VContS (c, s, t) :: vs) idc [] TNil m
  | (IControl (i), s) -> run_i10 i (VContC (c, s, t) :: vs) idc [] TNil m
  | (IShift0 (i), s) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_i10 i (VContS (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | (IControl0 (i), s) ->
    begin match m with
      MCons ((c0, s0, t0), m0) ->
      run_i10 i (VContC (c, s, t) :: vs) c0 s0 t0 m0
    | _ -> failwith "control0 is used without enclosing reset"
    end
  | (IReset (i), s) -> run_i10 i vs idc [] TNil (MCons ((c, s, t), m))
  | (ISeq (i0, i1), s) -> run_i10 i0 vs ((i1, vs) :: c) s t m

(* apply10 : v -> v -> c -> s -> t -> m -> v *)
and apply10 v0 v1 c s t m = match v0 with
    VFun (f) -> f c (v1 :: s) t m
  | VContS (c', s', t') -> run_c10 c' (v1 :: s') t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    run_c10 c' (v1 :: s')
           (apnd t' (cons (fun v t m -> run_c10 c (v :: s) t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply10s : v -> v list -> v list -> c -> s -> t -> m -> v *)
and apply10s v0 v2s vs c s t m = match v2s with
    [] -> run_c10 c (v0 :: s) t m
  | v1 :: v2s ->
    apply10 v0 v1 ((IApply, vs) :: c) (VArgs (v2s) :: s) t m

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = ISeq (i0, i1)

(* f10 : e -> string list -> i *)
let rec f10 e xs = match e with
    Num (n) -> INum (n)
  | Var (x) -> IAccess (Env.offset x xs)
  | Op (e0, op, e1) -> f10 e1 xs >> f10 e0 xs >> IOp (op)
  | Fun (x, e) -> IFun (f10 e (x :: xs))
  | App (e0, e2s) ->
    f10s e2s xs >> f10 e0 xs >> IApply
  | Shift (x, e) -> IShift (f10 e (x :: xs))
  | Control (x, e) -> IControl (f10 e (x :: xs))
  | Shift0 (x, e) -> IShift0 (f10 e (x :: xs))
  | Control0 (x, e) -> IControl0 (f10 e (x :: xs))
  | Reset (e) -> IReset (f10 e xs)

(* f10s : e list -> string list -> i *)
and f10s e2s xs = match e2s with
    [] -> IPushmark
  | e :: e2s -> f10s e2s xs >> f10 e xs >> IPush

(* f : e -> v *)
let f expr = run_i10 (f10 expr []) [] idc [] TNil MNil