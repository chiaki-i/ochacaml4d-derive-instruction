open Syntax
open Value

(* Definitional interpreter for λ-calculus with 4 delimited continuation operations : eval9c *)

(* initial continuation : c *)
let idc = C0

(* cons : h -> t -> t *)
let cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (Append (h, h'))

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* push : v -> s -> s *)
(* 引数スタック s の中の、先頭の引数列に値を追加する *)
let push v s = match s with
    [] -> failwith "s must be ((_ :: _) :: _), not []"
  | fst :: rest -> (v :: fst) :: rest

(* run_h : h -> v -> t -> m -> v *)
let rec run_h h v t m = match h with
    Hold (c, s) -> run_c c (push v s) t m
  | Append (h, h') -> run_h h v (cons h' t) m

(* run_c : c -> s -> t -> m -> v *)
and run_c c s t m = match (c, s) with
    (C0, (v :: []) :: s) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c c (push v s) t m
        end
      | Trail (h) -> run_h h v TNil m
    end
  | (CSeq (i, vs, c), s) ->
    begin match i with (* CSeq starts here *)
    INum (n) -> run_c c (push (VNum (n)) s) t m
  | IAccess (n) -> run_c c (push (List.nth vs n) s) t m
  | IOp (op) ->
    begin match s with (v :: v0 :: rest) :: s ->
        begin match (v, v0) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c c ((VNum (n0 + n1) :: rest) :: s) t m
              | Minus -> run_c c ((VNum (n0 - n1) :: rest) :: s) t m
              | Times -> run_c c ((VNum (n0 * n1) :: rest) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c c ((VNum (n0 / n1) :: rest) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
        end
      | _ -> failwith "IOp: unexpected s"
    end
  | ICur (i) ->
    run_c c (push (VFun (i, vs)) s) t m
  | IGrab (i) ->
    begin match s with
        [] :: s ->
        run_c c (push (VFun (i, vs)) s) t m
      | (v1 :: v2s') :: s ->
        run_c (CSeq (i, (v1 :: vs), c)) (v2s' :: s) t m
      | _ -> failwith "IGrab: unexpected s"
    end
  | IApply ->
    begin match s with
        (v :: v1 :: v2s) :: s -> app v v1 vs c (v2s :: s) t m
      | _ -> failwith "IApply: unexpected s"
    end
  | IReturn ->
    begin match s with
        (v :: v2s) :: s -> app_s v vs c (v2s :: s) t m
      | _ -> failwith "IReturn: unexpected s"
    end
  | IPushmark -> run_c c ([] :: s) t m
  | ISkip -> begin match s with v2s' :: s -> run_c c (v2s' :: s) t m end
  | IShift (i) ->
    run_c (CSeq (i, VContS (c, s, t) :: vs, idc)) [[]] TNil m
  | IControl (i) ->
    run_c (CSeq (i, VContC (c, s, t) :: vs, idc)) [[]] TNil m
  | IShift0 (i) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_c (CSeq (i, VContS (c, s, t) :: vs, c0)) s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | IControl0 (i) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        run_c (CSeq (i, VContC (c, s, t) :: vs, c0)) s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | IReset (i) ->
    run_c (CSeq (i, vs, idc)) [[]] TNil (MCons ((c, s, t), m))
  | ISeq (i0, i1) ->
    run_c (CSeq (i0, vs, (CSeq (i1, vs, c)))) s t m
  end
  | _ -> failwith "run_c: stack error"

(* app : v -> v -> v list -> c -> s -> t -> m -> v *)
and app v0 v1 vs c s t m =
  let app_c = CSeq (IReturn, vs, c) in
  match v0 with
    VFun (i, vs') -> run_c (CSeq (i, (v1 :: vs'), c)) s t m
  | VContS (c', s', t') ->
    run_c c' (push v1 s') t' (MCons ((app_c, s, t), m))
  | VContC (c', s', t') ->
    run_c c' (push v1 s') (apnd t' (cons (Hold (CSeq (IReturn, vs, c), s)) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* app_s : v -> v list -> c -> s -> t -> m -> v *)
and app_s v0 vs c (v2s :: s) t m = match v2s with
    [] -> run_c c (push v0 s) t m
  | v1 :: v2s -> app v0 v1 vs c (v2s :: s) t m

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = ISeq (i0, i1)

(* f : definitional interpreter *)
(* f : e -> string list -> i *)
let rec f e xs = match e with
    Num (n) -> INum (n)
  | Var (x) -> IAccess (Env.off_set x xs)
  | Op (e0, op, e1) ->
    f e1 xs >> f e0 xs >> IOp (op)
  | Fun (x, e) -> ICur (f_t e (x :: xs))
  | App (e0, e2s) ->
    f_s e2s xs >> f e0 xs >> IApply
  | Shift (x, e) -> IShift (f e (x :: xs))
  | Control (x, e) -> IControl (f e (x :: xs))
  | Shift0 (x, e) -> IShift0 (f e (x :: xs))
  | Control0 (x, e) -> IControl0 (f e (x :: xs))
  | Reset (e) -> IReset (f e xs)

(* f_t : e -> string list -> i *)
and f_t e xs = match e with
    Num (n) -> INum n >> IReturn
  | Var (x) -> IAccess (Env.off_set x xs) >> IReturn
  | Op (e0, op, e1) ->
    f e1 xs >> f e0 xs >> IOp (op) >> IReturn
  | Fun (x, e) -> IGrab (f_t e (x :: xs))
  | App (e0, e2s) -> f_st e2s xs >> f e0 xs >> IApply
  | Shift (x, e) -> IShift (f e (x :: xs)) >> IReturn
  | Control (x, e) -> IControl (f e (x :: xs)) >> IReturn
  | Shift0 (x, e) -> IShift0 (f e (x :: xs)) >> IReturn
  | Control0 (x, e) -> IControl0 (f e (x :: xs)) >> IReturn
  | Reset (e) -> IReset (f e xs) >> IReturn

(* f_s : e list -> string list -> i *)
and f_s e2s xs = match e2s with
    [] -> IPushmark
  | e :: e2s -> f_s e2s xs >> f e xs

(* f_st : e list -> string list -> i *)
and f_st e2s xs = match e2s with
    [] -> ISkip
  | e :: e2s -> f_st e2s xs >> f e xs

(* f_init : e -> v *)
let f_init expr = run_c (CSeq (f expr [], [], idc)) [[]] TNil MNil

