open Syntax
open Value

(* Interpreter using combinators factored as instructions : eval8s *)

let idc = []

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (Append (h, h'))

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_h9 : h -> v -> t -> m -> v *)
let rec run_h9 h v t m = match h with
    Hold (c, s) -> run_c9 c (v :: s) t m
  | Append (h, h') -> run_h9 h v (cons h' t) m

(* run_c9 : c -> s -> t -> m -> v *)
and run_c9 c s t m = match (c, s) with
    ([], v :: []) ->
    begin match t with
        TNil ->
        begin match m with
            [] -> v
          | (c, s, t) :: m -> run_c9 c (v :: s) t m
        end
      | Trail (h) -> run_h9 h v TNil m
    end
  | ((i1, vs) :: c, (v :: s)) ->
    run_i9 i1 vs c (v :: s) t m
  | _ -> failwith "run_c9 unexpected error"

and run_i9 i vs c s t m = match i with
    INum (n) -> run_c9 c (VNum (n) :: s) t m
  | IAccess (n) -> run_c9 c (List.nth vs n :: s) t m
  | IOp (op) ->
    begin match s with
        v0 :: v1 :: s ->
        begin match (v0, v1) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c9 c (VNum (n0 + n1) :: s) t m
              | Minus -> run_c9 c (VNum (n0 - n1) :: s) t m
              | Times -> run_c9 c (VNum (n0 * n1) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c9 c (VNum (n0 / n1) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                          ^ " are not numbers")
        end
      | _ -> failwith "stack error: op"
    end
  | IPushmark -> run_c9 c (VArgs ([]) :: s) t m
  | IPush ->
    begin match s with v :: VArgs (v2s) :: s ->
        run_c9 c (VArgs (v :: v2s) :: s) t m
      | _ -> failwith "stack error: IPush"
    end
  | IApply ->
    begin match s with
        v0 :: VArgs (v2s) :: s ->
          begin match v2s with
            [] -> run_c9 c (v0 :: s) t m
          | v1 :: v2s ->
            (* apply9 v0 v1 ((IApply, vs) :: c) (VArgs (v2s) :: s) t m *)
            begin match v0 with
                VFun (i, vs) ->
                  run_i9 i vs ((IApply, vs) :: c) (v1 :: VArgs (v2s) :: s) t m
              | VContS (c', s', t') ->
                run_c9 c' (v1 :: s') t'
                  ((((IApply, vs) :: c), (VArgs (v2s) :: s), t) :: m)
              | VContC (c', s', t') ->
                run_c9 c' (v1 :: s')
                  (apnd t' (cons (Hold (((IApply, vs) :: c), (VArgs (v2s) :: s))) t)) m
              | _ -> failwith (to_string v0
                              ^ " is not a function; it can not be applied.")
            end
          end
      | _ -> failwith "stack error: IApply"
    end
  | IFun (i) ->
    begin match (c, s) with
        ((IApply, vs') :: c', VArgs (v1 :: v2s) :: s') -> (* Grab *)
          (* print_endline ("grab: " ^ Value.s_to_string s); *)
        run_i9 i (v1 :: vs) ((IApply, vs') :: c') (VArgs (v2s) :: s') t m
      (* | ((i', vs') :: c', VArgs (v1 :: v2s) :: s') -> failwith "more arguments than required" *)
      | _ ->
        run_c9 c (VFun (i, vs) :: s) t m
    end
  | IShift (i) ->
    run_i9 i (VContS (c, s, t) :: vs) idc [] TNil m
  | IControl (i) ->
    run_i9 i (VContC (c, s, t) :: vs) idc [] TNil m
  | IShift0 (i) ->
    begin match m with
        (c0, s0, t0) :: m0 ->
        run_i9 i (VContS (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | IControl0 (i) ->
    begin match m with
        (c0, s0, t0) :: m0 ->
        run_i9 i (VContC (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | IReset (i) ->
    run_i9 i vs idc [] TNil ((c, s, t) :: m)
  | ISeq (i0, i1) ->
    run_i9 i0 vs ((i1, vs) :: c) s t m

(* apply9 : v -> v -> c -> s -> t -> m -> v *)
and apply9 v0 v1 c s t m = match v0 with
    VFun (i, vs) -> run_i9 i vs c (v1 :: s) t m
  | VContS (c', s', t') -> run_c9 c' (v1 :: s') t' ((c, s, t) :: m)
  | VContC (c', s', t') ->
    run_c9 c' (v1 :: s') (apnd t' (cons (Hold (c, s)) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply9s : v -> v list -> v list -> c -> s -> t -> m -> v *)
and apply9s v0 v2s vs c s t m = match v2s with
    [] -> run_c9 c (v0 :: s) t m
  | v1 :: v2s ->
    apply9 v0 v1 ((IApply, vs) :: c) (VArgs (v2s) :: s) t m

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
let f expr = run_i9 (f9 expr []) [] idc [] TNil []
