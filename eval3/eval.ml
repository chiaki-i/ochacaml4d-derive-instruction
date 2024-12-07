open Syntax
open Value

(* Linearized interpreter : eval3 *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c3 : c -> v -> t -> m -> v *)
let rec run_c3 c v t m = match c with
    [] ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, t), m) -> run_c3 c v t m
        end
      | Trail (h) -> h v TNil m
    end
  | CApp0 (v1) :: c -> apply3 v v1 c t m
  | CApp1 (e0, xs, vs) :: c ->
    f3 e0 xs vs (CApp0 (v) :: c) t m
  | COp0 (e0, xs, vs, op) :: c -> f3 e0 xs vs (COp1 (v, op) :: c) t m
  | COp1 (v0, op) :: c ->
    begin match (v, v0) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c3 c (VNum (n0 + n1)) t m
          | Minus -> run_c3 c (VNum (n0 - n1)) t m
          | Times -> run_c3 c (VNum (n0 * n1)) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c3 c (VNum (n0 / n1)) t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
(* | _ -> failwith "run_c3: unexpected continuation" *)

(* f3 : e -> string list -> v list -> c -> t -> m -> v *)
and f3 e xs vs c t m = match e with
    Num (n) -> run_c3 c (VNum (n)) t m
  | Var (x) -> run_c3 c (List.nth vs (Env.offset x xs)) t m
  | Op (e0, op, e1) -> f3 e1 xs vs (COp0 (e0, xs, vs, op) :: c) t m
  | Fun (x, e) ->
    begin match c with
      CApp0 (v1) :: c' -> (* Grab *)
             f3 e (x :: xs) (v1 :: vs) c' t m
    | _ -> run_c3 c (VFun (fun v1 c' t' m' ->
             f3 e (x :: xs) (v1 :: vs) c' t' m')) t m
    end
  | App (e0, e1, _) ->
    f3 e1 xs vs (CApp1 (e0, xs, vs) :: c) t m
  | Shift (x, e) -> f3 e (x :: xs) (VContS (c, t) :: vs) [] TNil m
  | Control (x, e) -> f3 e (x :: xs) (VContC (c, t) :: vs) [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) -> f3 e (x :: xs) (VContS (c, t) :: vs) c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) -> f3 e (x :: xs) (VContC (c, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f3 e xs vs [] TNil (MCons ((c, t), m))

(* apply3 : v -> v -> c -> t -> m -> v *)
and apply3 v0 v1 c t m = match v0 with
    VFun (f) -> f v1 c t m
  | VContS (c', t') -> run_c3 c' v1 t' (MCons ((c, t), m))
  | VContC (c', t') ->
    run_c3 c' v1 (apnd t' (cons (fun v t m -> run_c3 c v t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* f : e -> v *)
let f expr = f3 expr [] [] [] TNil MNil
