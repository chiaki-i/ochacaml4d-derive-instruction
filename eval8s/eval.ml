open Syntax
open Value

(* Interpreter using combinators factored as instructions : eval8s *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c8 : c -> s -> t -> m -> v *)
let rec run_c8 c s t m = match (c, s) with
    (C0, v :: []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c8 c (v :: s) t m
        end
      | Trail (h) -> h v TNil m
    end
  | (CSeq (i1, vs, c), (v :: s)) ->
    i1 vs c (v :: s) t m

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = fun vs c s t m ->
  i0 vs (CSeq (i1, vs, c)) s t m

(* num : int -> i *)
let num n = fun vs c s t m -> run_c8 c (VNum (n) :: s) t m

(* access : int -> i *)
let access n = fun vs c s t m -> run_c8 c (List.nth vs n :: s) t m

(* operation : op -> i *)
let operation op = fun vs c s t m -> match s with
    v0 :: v1 :: s ->
    begin match (v0, v1) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c8 c (VNum (n0 + n1) :: s) t m
          | Minus -> run_c8 c (VNum (n0 - n1) :: s) t m
          | Times -> run_c8 c (VNum (n0 * n1) :: s) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c8 c (VNum (n0 / n1) :: s) t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                       ^ " are not numbers")
    end
  | _ -> failwith "stack error: op"

(* pushmark : i *)
let pushmark = fun vs c s t m -> run_c8 c (VArgs ([]) :: s) t m

(* push : i *)
let push = fun vs c (v :: VArgs (v2s) :: s) t m ->
  run_c8 c (VArgs (v :: v2s) :: s) t m

(* apply8 : v -> v -> c -> s -> t -> m -> v *)
let apply8 v0 v1 c s t m = match v0 with
    VFun (f) -> f c (v1 :: s) t m
  | VContS (c', s', t') -> run_c8 c' (v1 :: s') t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    run_c8 c' (v1 :: s')
           (apnd t' (cons (fun v t m -> run_c8 c (v :: s) t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply8s : v -> v list -> v list -> c -> s -> t -> m -> v *)
let rec apply8s v0 v2s vs c s t m = match v2s with
    [] -> run_c8 c (v0 :: s) t m
  | v1 :: v2s ->
    apply8 v0 v1 (CSeq ((fun vs c (v :: VArgs (v2s) :: s) t m ->
      apply8s v v2s vs c s t m), vs, c)) (VArgs (v2s) :: s) t m

(* apply : i *)
let apply = fun vs c s t m -> match s with
  v0 :: VArgs (v2s) :: s -> apply8s v0 v2s vs c s t m

(* grab : i -> i *)
let grab i = fun vs c s t m ->
  begin match (c, s) with
      (CSeq (i', vs', c'), VArgs (v1 :: v2s) :: s') when i' == apply -> (*Grab*)
        (* print_endline ("grab: " ^ Value.s_to_string s); *)
        i (v1 :: vs) (CSeq (i', vs', c')) (VArgs (v2s) :: s') t m
    | _ ->
        let vfun = VFun (fun c' s' t' m' ->
          begin match s' with
            v1 :: s' -> i (v1 :: vs) c' s' t' m'
          | _ -> failwith "stack error"
          end) in
        run_c8 c (vfun :: s) t m
  end

(* shift : i -> i *)
let shift i = fun vs c s t m ->
  i (VContS (c, s, t) :: vs) C0 [] TNil m

(* control : i -> i *)
let control i = fun vs c s t m ->
  i (VContC (c, s, t) :: vs) C0 [] TNil m

(* shift0 : i -> i *)
let shift0 i = fun vs c s t m -> match m with
    MCons ((c0, s0, t0), m0) ->
    i (VContS (c, s, t) :: vs) c0 s0 t0 m0
  | _ -> failwith "shift0 is used without enclosing reset"

(* control0 : i -> i *)
let control0 i = fun vs c s t m -> match m with
    MCons ((c0, s0, t0), m0) ->
    i (VContC (c, s, t) :: vs) c0 s0 t0 m0
  | _ -> failwith "control0 is used without enclosing reset"

(* reset : i -> i *)
let reset i = fun vs c s t m ->
  i vs C0 [] TNil (MCons ((c, s, t), m))

(* f8 : e -> string list -> i *)
let rec f8 e xs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.offset x xs)
  | Op (e0, op, e1) -> f8 e1 xs >> f8 e0 xs >> operation (op)
  | Fun (x, e) -> grab (f8 e (x :: xs))
  | App (e0, e2s) ->
    f8s e2s xs >> f8 e0 xs >> apply
  | Shift (x, e) -> shift (f8 e (x :: xs))
  | Control (x, e) -> control (f8 e (x :: xs))
  | Shift0 (x, e) -> shift0 (f8 e (x :: xs))
  | Control0 (x, e) -> control0 (f8 e (x :: xs))
  | Reset (e) -> reset (f8 e xs)

(* f8s : e list -> string list -> i *)
and f8s e2s xs = match e2s with
    [] -> pushmark
  | e :: e2s -> f8s e2s xs >> f8 e xs >> push

(* f : e -> v *)
let f expr = f8 expr [] [] C0 [] TNil MNil