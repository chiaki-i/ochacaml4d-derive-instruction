open Syntax
open Value

(* Defunctionalized interpreter with values passed via stack : eval7d *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c7 : c -> s -> r -> t -> m -> v *)
let rec run_c7 c s r t m = match (c, s, r) with
    (C0, v :: [], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, r, t), m) -> run_c7 c (v :: s) r t m
        end
      | Trail (h) -> h v TNil m
    end
  | (CApp0 (c), v :: VArg (v1) :: s, r) ->
    apply7 v v1 c s r t m
  | (CApp1 (f_e0_xs, c), v :: s, VEnv (vs) :: r) ->
    f_e0_xs vs (CApp0 (c)) (VArg (v) :: s) r t m
  | (COpP0 (c), v :: v1 :: s, r) ->
    apply_op7 Plus v v1 c s r t m
  | (COpP1 (f_e0_xs, c), v :: s, VEnv (vs) :: r) ->
    f_e0_xs vs (COpP0 (c)) (v :: s) r t m
  | (COpM0 (c), v :: v1 :: s, r) ->
    apply_op7 Minus v v1 c s r t m
  | (COpM1 (f_e0_xs, c), v :: s, VEnv (vs) :: r) ->
    f_e0_xs vs (COpM0 (c)) (v :: s) r t m
  | (COpT0 (c), v :: v1 :: s, r) ->
    apply_op7 Times v v1 c s r t m
  | (COpT1 (f_e0_xs, c), v :: s, VEnv (vs) :: r) ->
    f_e0_xs vs (COpT0 (c)) (v :: s) r t m
  | (COpD0 (c), v :: v1 :: s, r) ->
    apply_op7 Divide v v1 c s r t m
  | (COpD1 (f_e0_xs, c), v :: s, VEnv (vs) :: r) ->
    f_e0_xs vs (COpD0 (c)) (v :: s) r t m
  | _ -> failwith "stack or cont error"

(* f7 : e -> string list -> v list -> c -> s -> r -> t -> m -> v *)
and f7 e xs vs c s r t m = match e with
    Num (n) -> run_c7 c (VNum (n) :: s) r t m
  | Var (x) -> run_c7 c (List.nth vs (Env.offset x xs) :: s) r t m
  | Op (e0, Plus, e1) ->
    let f_e1_xs = f7 e1 xs in
    let f_e0_xs = f7 e0 xs in
    f_e1_xs vs (COpP1 (f_e0_xs, c)) s (VEnv (vs) :: r) t m
  | Op (e0, Minus, e1) ->
    let f_e1_xs = f7 e1 xs in
    let f_e0_xs = f7 e0 xs in
    f_e1_xs vs (COpM1 (f_e0_xs, c)) s (VEnv (vs) :: r) t m
  | Op (e0, Times, e1) ->
    let f_e1_xs = f7 e1 xs in
    let f_e0_xs = f7 e0 xs in
    f_e1_xs vs (COpT1 (f_e0_xs, c)) s (VEnv (vs) :: r) t m
  | Op (e0, Divide, e1) ->
    let f_e1_xs = f7 e1 xs in
    let f_e0_xs = f7 e0 xs in
    f_e1_xs vs (COpD1 (f_e0_xs, c)) s (VEnv (vs) :: r) t m
  | Fun (x, e) ->
    begin match (c, s, r) with
      (CApp0 (c'),  VArg (v1) :: s', r) -> (* Grab *)
             f7 e (x :: xs) (v1 :: vs) c' s' r t m
    | _ -> run_c7 c (VFun (fun c' (v1 :: s') r' t' m' ->
             f7 e (x :: xs) (v1 :: vs) c' s' r' t' m') :: s) r t m
    end
  | App (e0, e1, e2s) ->
    let f_e1_xs = f7 e1 xs in
    let f_e0_xs = f7 e0 xs in
    f_e1_xs vs (CApp1 (f_e0_xs, c)) s (VEnv (vs) :: r) t m
  | Shift (x, e) -> f7 e (x :: xs) (VContS (c, s, r, t) :: vs) C0 [] [] TNil m
  | Control (x, e) -> f7 e (x :: xs) (VContC (c, s, r, t) :: vs) C0 [] [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        f7 e (x :: xs) (VContS (c, s, r, t) :: vs) c0 s0 r0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        f7 e (x :: xs) (VContC (c, s, r, t) :: vs) c0 s0 r0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f7 e xs vs C0 [] [] TNil (MCons ((c, s, r, t), m))

(* apply7 : v -> v -> c -> s -> r -> t -> m -> v *)
and apply7 v0 v1 c s r t m = match v0 with
    VFun (f) -> f c (v1 :: s) r t m
  | VContS (c', s', r', t') ->
    run_c7 c' (v1 :: s') r' t' (MCons ((c, s, r, t), m))
  | VContC (c', s', r', t') ->
    run_c7 c' (v1 :: s') r'
           (apnd t' (cons (fun v t m -> run_c7 c (v :: s) r t m) t)) m
  | _ -> failwith (to_string v0
                    ^ " is not a function; it can not be applied.")

and apply_op7 op v0 v1 c s1 r1 t1 m1 = match (v0, v1) with
    (VNum (n0), VNum (n1)) ->
    begin match op with
      Plus -> run_c7 c (VNum (n0 + n1) :: s1) r1 t1 m1
    | Minus -> run_c7 c (VNum (n0 - n1) :: s1) r1 t1 m1
    | Times -> run_c7 c (VNum (n0 * n1) :: s1) r1 t1 m1
    | Divide ->
      if n1 = 0 then failwith "Division by zero"
      else run_c7 c (VNum (n0 / n1) :: s1) r1 t1 m1
    end
  | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                   ^ " are not numbers")

(* f : e -> v *)
let f expr = f7 expr [] [] C0 [] [] TNil MNil
