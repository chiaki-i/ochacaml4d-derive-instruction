open Syntax
open Value

(* Interpreter using combinators factored as instructions : eval8 *)

(* initial continuation : s -> t -> m -> v *)
(*
let idc s r t m = match (s, r) with
    (v :: [], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, r, t), m) -> c (v :: s) r t m
        end
      | Trail (h) -> h v TNil m
    end
  | _ -> failwith "stack error: idc"
*)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = fun vs c s r t m ->
  i0 vs (CRest (i1, c)) s (VEnv (vs) :: r) t m

(* num : int -> i *)
let rec num n = fun vs c s r t m -> run_c8 c (VNum (n) :: s) r t m

(* access : int -> i *)
and access n = fun vs c s r t m -> run_c8 c (List.nth vs n :: s) r t m

(* operation : op -> i *)
and operation op = fun vs c s r t m -> match (s, r) with
    (v0 :: v1 :: s, r) ->
    begin match (v0, v1) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c8 c (VNum (n0 + n1) :: s) r t m
          | Minus -> run_c8 c (VNum (n0 - n1) :: s) r t m
          | Times -> run_c8 c (VNum (n0 * n1) :: s) r t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c8 c (VNum (n0 / n1) :: s) r t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                       ^ " are not numbers")
    end
  | _ -> failwith "stack error: op"

(* grab : i -> i *)
and grab i = fun vs c s r t m ->
  begin match (c, s, r) with
      (CApp0 (c'), VArg (v1) :: s', r) -> (* Grab *)
        print_endline "here";
        i (v1 :: vs) c' s' r t m
    | _ ->
        let vfun = VFun (fun c' s' r' t' m' ->
          begin match (s', r') with
            (v :: s', r') -> i (v :: vs) c' s' r' t' m'
          | _ -> failwith "stack error"
          end) in
        run_c8 c (vfun :: s) r t m
  end

(* apply8 : v -> v -> c -> s -> r -> t -> m -> v *)
and apply8 v0 v1 c s r t m = match v0 with
    VFun (f) -> f c (v1 :: s) r t m
  | VContS (c', s', r', t') ->
    run_c8 c' (v1 :: s') r' t' (MCons ((c, s, r, t), m))
  | VContC (c', s', r', t') ->
    run_c8 c' (v1 :: s') r'
           (apnd t' (cons (fun v t m -> run_c8 c (v :: s) r t m) t)) m
  | _ -> failwith (to_string v0
                    ^ " is not a function; it cannot be applied.")

(* apply : i *)
and apply = fun vs c s r t m -> match (s, r) with
  (v0 :: v1 :: s, r) -> apply8 v0 v1 c s r t m

(* shift : i -> i *)
and shift i = fun vs c s r t m ->
  i (VContS (c, s, r, t) :: vs) C0 [] [] TNil m

(* control : i -> i *)
and control i = fun vs c s r t m ->
  i (VContC (c, s, r, t) :: vs) C0 [] [] TNil m

(* shift0 : i -> i *)
and shift0 i = fun vs c s r t m -> match m with
    MCons ((c0, s0, r0, t0), m0) ->
    i (VContS (c, s, r, t) :: vs) c0 s0 r0 t0 m0
  | _ -> failwith "shift0 is used without enclosing reset"

(* control0 : i -> i *)
and control0 i = fun vs c s r t m -> match m with
    MCons ((c0, s0, r0, t0), m0) ->
    i (VContC (c, s, r, t) :: vs) c0 s0 r0 t0 m0
  | _ -> failwith "control0 is used without enclosing reset"

(* reset : i -> i *)
and reset i = fun vs c s r t m ->
  i vs C0 [] [] TNil (MCons ((c, s, r, t), m))

(* run_c8 : c -> s -> r -> t -> m -> v *)
and run_c8 c s r t m = match (c, s, r) with
    (C0, v :: [], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, r, t), m) -> run_c8 c (v :: s) r t m
        end
      | Trail (h) -> h v TNil m
    end
  | (CRest (i1, c'), s', VEnv (vs) :: r') -> i1 vs c s' r' t m
(*   (fun s' (VEnv (vs) :: r') t' m' -> i1 vs c s' r' t' m') *)
  | (CApp0 (c), v :: VArg (v1) :: s, r) ->
    apply8 v v1 c s r t m
  | (CApp1 (e0, xs, c), v :: s, VEnv (vs) :: r) ->
    f8 e0 xs vs (CApp0 (c)) (VArg (v) :: s) r t m
  | (COp0 (e0, xs, op, c), v :: s, VEnv (vs) :: r) ->
    f8 e0 xs vs (COp1 (op, c)) (v :: s) r t m
  | (COp1 (op, c), v :: v0 :: s, r) ->
    begin match (v, v0) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c8 c (VNum (n0 + n1) :: s) r t m
          | Minus -> run_c8 c (VNum (n0 - n1) :: s) r t m
          | Times -> run_c8 c (VNum (n0 * n1) :: s) r t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c8 c (VNum (n0 / n1) :: s) r t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
  | _ -> failwith "stack or cont error"

(* f8 : e -> string list -> i *)
and f8 e xs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.offset x xs)
  | Op (e0, op, e1) ->
    f8 e1 xs >> f8 e0 xs >> operation (op)
  | Fun (x, e) -> grab (f8 e (x :: xs))
  | App (e0, e1, _) ->
    f8 e1 xs >> f8 e0 xs >> apply
  | Shift (x, e) -> shift (f8 e (x :: xs))
  | Control (x, e) -> control (f8 e (x :: xs))
  | Shift0 (x, e) -> shift0 (f8 e (x :: xs))
  | Control0 (x, e) -> control0 (f8 e (x :: xs))
  | Reset (e) -> reset (f8 e xs)

(* f : e -> v *)
let f expr = f8 expr [] [] C0 [] [] TNil MNil
