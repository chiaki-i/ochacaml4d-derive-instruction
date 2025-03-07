open Syntax
open Value

(* Stack-based interpreter : eval4 (without return stack) *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c4 : c -> v -> s -> t -> m -> v *)
let rec run_c4 c v s t m = match (c, s) with
    ([], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c4 c v s t m
        end
      | Trail (h) -> h v TNil m
    end
  | (CApp0 :: c, VArg (v1) :: s) ->
    apply4 v v1 c s t m
  | (CApp1 (e0, xs, vs) :: c, s) ->
    f4 e0 xs vs (CApp0 :: c) (VArg (v) :: s) t m
  | (COp0 (e0, xs, vs, op) :: c, s) ->
    f4 e0 xs vs (COp1 (op) :: c) (v :: s) t m
  | (COp1 (op) :: c, v0 :: s) ->
    begin match (v, v0) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c4 c (VNum (n0 + n1)) s t m
          | Minus -> run_c4 c (VNum (n0 - n1)) s t m
          | Times -> run_c4 c (VNum (n0 * n1)) s t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c4 c (VNum (n0 / n1)) s t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
  | _ -> failwith "stack or cont error"

(* apply4 : v -> v -> c -> s -> t -> m -> v *)
and apply4 v0 v1 c s t m = match v0 with
    VFun (f) -> f v1 c s t m
  | VContS (c', s', t') -> run_c4 c' v1 s' t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    run_c4 c' v1 s' (apnd t' (cons (fun v t m -> run_c4 c v s t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* f4 : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f4 e xs vs c s t m = match e with
    Num (n) -> run_c4 c (VNum (n)) s t m
  | Var (x) -> run_c4 c (List.nth vs (Env.offset x xs)) s t m
  | Op (e0, op, e1) ->
    f4 e1 xs vs (COp0 (e0, xs, vs, op) :: c) s t m
  | Fun (x, e) ->
    begin match (c, s) with
      (CApp0 :: c', VArg (v1) :: s') -> (* Grab *)
             f4 e (x :: xs) (v1 :: vs) c' s' t m
    | _ -> run_c4 c (VFun (fun v1 c' s' t' m' ->
             f4 e (x :: xs) (v1 :: vs) c' s' t' m')) s t m
    end
  | App (e0, e1, _) ->
    f4 e1 xs vs (CApp1 (e0, xs, vs) :: c) s t m
  | Shift (x, e) -> f4 e (x :: xs) (VContS (c, s, t) :: vs) [] [] TNil m
  | Control (x, e) -> f4 e (x :: xs) (VContC (c, s, t) :: vs) [] [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f4 e (x :: xs) (VContS (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f4 e (x :: xs) (VContC (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f4 e xs vs [] [] TNil (MCons ((c, s, t), m))

(* f : e -> v *)
let f expr = f4 expr [] [] [] [] TNil MNil
