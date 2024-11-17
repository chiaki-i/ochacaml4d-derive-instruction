open Syntax
open Value

(* Defunctionalized interpreter : eval2 *)

(* initial continuation *)
let idc = C0

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c2 : c -> v -> t -> m -> v *)
let rec run_c2 c v t m = match c with
    C0 ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, t), m) -> run_c2 c v t m
        end
      | Trail (h) -> h v TNil m
    end
  | CApp0 (v1, c) -> apply2 v v1 c t m
  | CApp1 (f_e0_xs, vs, c) ->
    f_e0_xs vs (CApp0 (v, c)) t m
  | COp0 (v1, apply_op, c) -> apply_op v v1 c t m
  | COp1 (f_e0_xs, vs, apply_op, c) -> f_e0_xs vs (COp0 (v, apply_op, c)) t m

(* f2 : e -> string list -> v list -> c -> t -> m -> v *)
and f2 e xs vs c t m = match e with
    Num (n) -> run_c2 c (VNum (n)) t m
  | Var (x) -> run_c2 c (List.nth vs (Env.offset x xs)) t m
  | Op (e0, op, e1) ->
    let f_e1_xs = f2 e1 xs in
    let f_e0_xs = f2 e0 xs in
    let apply_op = apply_op2 op in
    f_e1_xs vs (COp1 (f_e0_xs, vs, apply_op, c)) t m
  | Fun (x, e) ->
    begin match c with
      CApp0 (v1, c') -> (* Grab *)
             f2 e (x :: xs) (v1 :: vs) c' t m
    | _ -> run_c2 c (VFun (fun v1 c' t' m' ->
             f2 e (x :: xs) (v1 :: vs) c' t' m')) t m
    end
  | App (e0, e1, _) ->
    let f_e1_xs = f2 e1 xs in
    let f_e0_xs = f2 e0 xs in
    f_e1_xs vs (CApp1 (f_e0_xs, vs, c)) t m
  | Shift (x, e) -> f2 e (x :: xs) (VContS (c, t) :: vs) idc TNil m
  | Control (x, e) -> f2 e (x :: xs) (VContC (c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) -> f2 e (x :: xs) (VContS (c, t) :: vs) c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) -> f2 e (x :: xs) (VContC (c, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f2 e xs vs idc TNil (MCons ((c, t), m))

(* apply2 : v -> v -> c -> t -> m -> v *)
and apply2 v0 v1 c t m = match v0 with
    VFun (f) -> f v1 c t m
  | VContS (c', t') -> run_c2 c' v1 t' (MCons ((c, t), m))
  | VContC (c', t') ->
    run_c2 c' v1 (apnd t' (cons (fun v t m -> run_c2 c v t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it cannot be applied.")

and apply_op2 op v0 v1 c t1 m1 = match (v0, v1) with
    (VNum (n0), VNum (n1)) ->
    begin match op with
      Plus -> run_c2 c (VNum (n0 + n1)) t1 m1
    | Minus -> run_c2 c (VNum (n0 - n1)) t1 m1
    | Times -> run_c2 c (VNum (n0 * n1)) t1 m1
    | Divide ->
      if n1 = 0 then failwith "Division by zero"
      else run_c2 c (VNum (n0 / n1)) t1 m1
    end
  | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                   ^ " are not numbers")

(* f : e -> v *)
let f expr = f2 expr [] [] idc TNil MNil
