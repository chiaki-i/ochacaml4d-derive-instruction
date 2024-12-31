open Syntax
open Value

(* Interpreter using combinators factored as instructions : eval9s *)

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
    (C0, v :: [], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, r, t), m) -> run_c9 c (v :: s) r t m
        end
      | Trail (h) -> h v TNil m
    end
  | (CSeq (i1, vs, c), (v :: s), r) ->
    i1 vs c (v :: s) r t m

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = fun vs c s r t m ->
  i0 vs (CSeq (i1, vs, c)) s r t m

(* num : int -> i *)
let num n = fun vs c s r t m -> run_c9 c (VNum (n) :: s) r t m

(* access : int -> i *)
let access n = fun vs c s r t m -> run_c9 c (List.nth vs n :: s) r t m

(* operation : op -> i *)
let operation op = fun vs c s r t m -> match s with
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

(* pushmark : i *)
let pushmark = fun vs c s r t m -> run_c9 c (VArgs ([]) :: s) r t m

(* push : i *)
let push = fun vs c (v :: VArgs (v2s) :: s) r t m ->
  run_c9 c (VArgs (v :: v2s) :: s) r t m

(* apply : i *)
let rec apply = fun vs c s r t m -> match s with
  v0 :: VArgs (v2s) :: s ->
    begin match v2s with
        [] -> run_c9 c (v0 :: s) r t m
      | v1 :: v2s ->
        begin match v0 with
            VFun (f) -> f C0 (v1 :: VArgs (v2s) :: s) (VK (CSeq (apply, vs, c)) :: r) t m
          | VContS (c', s', r', t') ->
            run_c9 c' (v1 :: s') r' t' (MCons ((CSeq (apply, vs, c), VArgs (v2s) :: s, r, t), m))
          | VContC (c', s', r', t') ->
            run_c9 c' (v1 :: s') r'
                  (apnd t' (cons (fun v t m -> run_c9 (CSeq (apply, vs, c)) (v :: VArgs (v2s) :: s) r t m) t)) m
          | _ -> failwith (to_string v0
                          ^ " is not a function; it can not be applied.")
        end
    end

(* grab : i -> i *)
let grab i = fun vs c s r t m ->
  begin match (c, s, r) with
      (CSeq (i', vs', c'), VArgs (v1 :: v2s) :: s', r') when i' == apply ->
        (* print_endline ("grab: " ^ Value.s_to_string s); *)
        i (v1 :: vs) (CSeq (i', vs', c')) (VArgs (v2s) :: s') r' t m (*Grab*)
    | _ ->
        let vfun = VFun (fun _ s' (VK (c') :: r') t' m' ->
          begin match s' with
            v1 :: s' -> i (v1 :: vs) c' s' r' t' m'
          | _ -> failwith "stack error"
          end) in
        run_c9 c (vfun :: s) r t m
  end

(* shift : i -> i *)
let shift i = fun vs c s r t m ->
  i (VContS (c, s, r, t) :: vs) C0 [] [] TNil m

(* control : i -> i *)
let control i = fun vs c s r t m ->
  i (VContC (c, s, r, t) :: vs) C0 [] [] TNil m

(* shift0 : i -> i *)
let shift0 i = fun vs c s r t m -> match m with
    MCons ((c0, s0, r0, t0), m0) ->
    i (VContS (c, s, r, t) :: vs) c0 s0 r0 t0 m0
  | _ -> failwith "shift0 is used without enclosing reset"

(* control0 : i -> i *)
let control0 i = fun vs c s r t m -> match m with
    MCons ((c0, s0, r0, t0), m0) ->
    i (VContC (c, s, r, t) :: vs) c0 s0 r0 t0 m0
  | _ -> failwith "control0 is used without enclosing reset"

(* reset : i -> i *)
let reset i = fun vs c s r t m ->
  i vs C0 [] [] TNil (MCons ((c, s, r, t), m))

(* f9 : e -> string list -> i *)
let rec f9 e xs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.offset x xs)
  | Op (e0, op, e1) -> f9 e1 xs >> f9 e0 xs >> operation (op)
  | Fun (x, e) -> grab (f9 e (x :: xs))
  | App (e0, e2s) ->
    f9s e2s xs >> f9 e0 xs >> apply
  | Shift (x, e) -> shift (f9 e (x :: xs))
  | Control (x, e) -> control (f9 e (x :: xs))
  | Shift0 (x, e) -> shift0 (f9 e (x :: xs))
  | Control0 (x, e) -> control0 (f9 e (x :: xs))
  | Reset (e) -> reset (f9 e xs)

(* f9s : e list -> string list -> i *)
and f9s e2s xs = match e2s with
    [] -> pushmark
  | e :: e2s -> f9s e2s xs >> f9 e xs >> push

(* f : e -> v *)
let f expr = f9 expr [] [] C0 [] [] TNil MNil
