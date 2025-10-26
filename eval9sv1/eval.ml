open Syntax
open Value

(* Defuntionalized instructions : eval9sv *)
(* Derived from eval8sv *)

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
    (idc, v :: [], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, r, t), m) -> run_c9 c (v :: s) r t m
        end
      | Trail (h) -> h v TNil m
    end
  | (i1 :: c, (v :: s), rv :: r) ->
    run_i9 i1 rv c (v :: s) r t m

(* (>>) : i -> i -> i *)
and (>>) i0 i1 = ISeq (i0, i1)

and run_i9 i rv c s r t m = match (i, rv) with
    (INum (n), _) -> run_c9 c (VNum (n) :: s) r t m
  | (IAccess (n), VS (vs)) -> run_c9 c (List.nth vs n :: s) r t m
  | (IOp (op), VS (vs)) ->
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
  | (IPushmark, VS (vs)) -> run_c9 c (VArgs ([]) :: s) r t m
  | (IPush, VS (vs)) ->
    begin match s with v :: VArgs (v2s) :: s ->
      run_c9 c (VArgs (v :: v2s) :: s) r t m
    end
  | (IApply, VS (vs)) ->
    begin match s with
        v0 :: VArgs ([]) :: s ->
        run_c9 c (v0 :: s) r t m
      | VFun (f) :: VArgs (v1 :: v2s) :: s ->
        f (IApply :: c) (v1 :: VArgs (v2s) :: s) (VS (vs) :: r) t m
      | VContS (c', s', r', t') :: VArgs (v1 :: v2s) :: s ->
        run_c9 c' (v1 :: s') r' t' (MCons ((IApply :: c, VArgs (v2s) :: s, VS (vs) :: r, t), m))
      | VContC (c', s', r', t') :: VArgs (v1 :: v2s) :: s ->
        run_c9 c' (v1 :: s') r'
              (apnd t' (cons (fun v t m -> run_c9 (IApply :: c) (v :: VArgs (v2s) :: s) (VS (vs) :: r) t m) t)) m
      | v0 :: VArgs (v1 :: v2s) :: s ->
        failwith (to_string v0 ^ " is not a function; it can not be applied.")
    end
  | (IFun (i), VS (vs)) ->
    begin match (c, s, r) with
        (i' :: c', VArgs (v1 :: v2s) :: s', VS (vs') :: r')
          when i' == IApply -> (*Grab*)
          (* print_endline ("grab: " ^ Value.s_to_string s); *)
          run_i9 i (VS (v1 :: vs)) (i' :: c') (VArgs (v2s) :: s')
            (VS (vs') :: r') t m
      | _ ->
          let vfun = VFun (fun c' s' r' t' m' ->
            begin match s' with
              v1 :: s' -> run_i9 i (VS (v1 :: vs)) c' s' r' t' m'
            | _ -> failwith "stack error"
            end) in
          run_c9 c (vfun :: s) r t m
    end
  | (IShift (i), VS (vs)) ->
    run_i9 i (VS (VContS (c, s, r, t) :: vs)) idc [] [] TNil m
  | (IControl (i), VS (vs)) ->
    run_i9 i (VS (VContC (c, s, r, t) :: vs)) idc [] [] TNil m
  | (IShift0 (i), VS (vs)) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        run_i9 i (VS (VContS (c, s, r, t) :: vs)) c0 s0 r0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | (IControl0 (i), VS (vs)) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        run_i9 i (VS (VContC (c, s, r, t) :: vs)) c0 s0 r0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | (IReset (i), VS (vs)) ->
    run_i9 i (VS (vs)) idc [] [] TNil (MCons ((c, s, r, t), m))
  | (ISeq (i0, i1), rv) ->
    run_i9 i0 rv (i1 :: c) s (rv :: r) t m

(* f : e -> string list -> i *)
let rec f e xs = match e with
    Num (n) -> INum (n)
  | Var (x) -> IAccess (Env.off_set x xs)
  | Op (e0, op, e1) -> f e1 xs >> f e0 xs >> IOp (op)
  | Fun (x, e) -> IFun (f e (x :: xs))
  | App (e0, e2s) ->
    f_s e2s xs >> f e0 xs >> IApply
  | Shift (x, e) -> IShift (f e (x :: xs))
  | Control (x, e) -> IControl (f e (x :: xs))
  | Shift0 (x, e) -> IShift0 (f e (x :: xs))
  | Control0 (x, e) -> IControl0 (f e (x :: xs))
  | Reset (e) -> IReset (f e xs)

(* f_s : e list -> string list -> i *)
and f_s e2s xs = match e2s with
    [] -> IPushmark
  | e :: e2s -> f_s e2s xs >> f e xs >> IPush

(* f_init : e -> v *)
let f_init expr = run_i9 (f expr []) (VS ([])) idc [] [] TNil MNil
