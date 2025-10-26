open Syntax
open Value

(* Interpreter using combinators factored as instructions : eval8 *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* (>>) : i -> i -> i *)
let (>>!) i0 i1 = fun vs c s r t m ->
  i0 vs (CApp1 (i1, c)) s (VEnv (vs) :: r) t m

let (>>@) i0 i1 = fun vs c s r t m ->
  i0 vs (CApp0 (i1, c)) s (VEnv (vs) :: r) t m

(*
let (>>+) i0 i1 = fun vs c s r t m ->
  i0 vs (COp1 (i1, app_op, c)) s (VEnv (vs) :: r) t m

let (>>* ) i0 i1 = fun vs c s r t m ->
  i0 vs (COp0 (i1, c)) s (VEnv (vs) :: r) t m
*)

(* num : int -> i *)
let rec num n = fun vs c s r t m -> run_c8 c (VNum (n) :: s) r t m

(* access : int -> i *)
and access n = fun vs c s r t m -> run_c8 c (List.nth vs n :: s) r t m

(* app_op8 : op -> v -> v -> c -> s -> r -> t -> m -> v *)
and app_op8 op v0 v1 c s1 r1 t1 m1 = match (v0, v1) with
    (VNum (n0), VNum (n1)) ->
    begin match op with
      Plus -> run_c8 c (VNum (n0 + n1) :: s1) r1 t1 m1
    | Minus -> run_c8 c (VNum (n0 - n1) :: s1) r1 t1 m1
    | Times -> run_c8 c (VNum (n0 * n1) :: s1) r1 t1 m1
    | Divide ->
      if n1 = 0 then failwith "Division by zero"
      else run_c8 c (VNum (n0 / n1) :: s1) r1 t1 m1
    end
  | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                   ^ " are not numbers")

(* app_op : op -> i *)
and app_op op = fun vs c s r t m -> match (s, r) with
  (v0 :: v1 :: s, r) -> app_op8 op v0 v1 c s r t m

(* grab : i -> i *)
and grab i = fun vs c s r t m ->
  begin match (c, s, r) with
  (*
      (CApp0 (app, c'), VArg (v1) :: s', r) -> (* Grab *)
        print_endline "here";
        i (v1 :: vs) c' s' r t m
        *)
    | _ ->
        let vfun = VFun (fun c' s' r' t' m' ->
          begin match (s', r') with
            (v :: s', r') -> i (v :: vs) c' s' r' t' m'
          | _ -> failwith "stack error"
          end) in
        run_c8 c (vfun :: s) r t m
  end

(* app : v -> v -> c -> s -> r -> t -> m -> v *)
and app v0 v1 c s r t m = match v0 with
    VFun (f) -> f c (v1 :: s) r t m
  | VContS (c', s', r', t') ->
    run_c8 c' (v1 :: s') r' t' (MCons ((c, s, r, t), m))
  | VContC (c', s', r', t') ->
    run_c8 c' (v1 :: s') r'
           (apnd t' (cons (fun v t m -> run_c8 c (v :: s) r t m) t)) m
  | _ -> failwith (to_string v0
                    ^ " is not a function; it cannot be applied.")

(* app : i *)
and app = fun vs c s r t m -> match (s, r) with
  (v0 :: VArg (v1) :: s, r) -> app v0 v1 c s r t m

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
  | (CApp1 (i, c), v :: s, VEnv (vs) :: r) ->
    i vs (CApp0 (app, c)) (VArg (v) :: s) (VEnv (vs) :: r) t m
  | (CApp0 (app, c), v :: VArg (v1) :: s, VEnv (vs) :: r) ->
    app vs c (v :: VArg (v1) :: s) r t m
(*
  | (COp1 (i1, c), v :: s, VEnv (vs) :: r) ->
    i1 vs (COp0 (c)) (v :: s) r t m
  | (COp0 (c), v :: v0 :: s, VEnv (vs) :: r) ->
    i vs c (v :: v0 :: s) r t m
  | _ -> failwith "stack or cont error"
*)

(* f : e -> string list -> i *)
and f e xs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.off_set x xs)
  (*
  | Op (e0, op, e1) ->
    f e1 xs >>+ f e0 xs >>* app_op op
    *)
  | Fun (x, e) -> grab (f e (x :: xs))
  | App (e0, e1, _) ->
    f e1 xs >>! f e0 xs >>@ app
  | Shift (x, e) -> shift (f e (x :: xs))
  | Control (x, e) -> control (f e (x :: xs))
  | Shift0 (x, e) -> shift0 (f e (x :: xs))
  | Control0 (x, e) -> control0 (f e (x :: xs))
  | Reset (e) -> reset (f e xs)

(* f_init : e -> v *)
let f_init expr = f expr [] [] C0 [] [] TNil MNil
