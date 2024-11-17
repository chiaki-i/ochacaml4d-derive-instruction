open Syntax
open Value

(* Refunctionalized interpreter with values passed via stack : eval7r *)

(* initial continuation : v -> s -> r -> t -> m -> v *)
let idc (v :: s) r t m = match (s, r) with
    ([], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, r, t), m) -> c (v :: s) r t m
        end
      | Trail (h) -> h v TNil m
    end
  | _ -> failwith "stack error idc"

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* f7 : e -> string list -> v list -> c -> s -> r -> t -> m -> v *)
let rec f7 e xs vs c s r t m = match e with
    Num (n) -> c (VNum (n) :: s) r t m
  | Var (x) -> c (List.nth vs (Env.offset x xs) :: s) r t m
  | Op (e0, op, e1) ->
    let f_e1_xs = f7 e1 xs in
    let f_e0_xs = f7 e0 xs in
    f_e1_xs vs (fun (v1 :: s1) (VEnv (vs) :: r1) t1 m1 ->
        f_e0_xs vs (fun (v0 :: v1 :: s0) r0 t0 m0 ->
            apply_op7 op v0 v1 c s0 r0 t0 m0
        ) (v1 :: s1) r1 t1 m1
    ) s (VEnv (vs) :: r) t m
  | Fun (x, e) ->
    begin match (s, r) with
    (*
      (VArg (v1, c') :: s', r) -> (* Grab *)
             f7 e (x :: xs) (v1 :: vs) c' s' r t m
    *)
    | _ -> c (VFun (fun c' (v1 :: s') r' t' m' ->
             f7 e (x :: xs) (v1 :: vs) c' s' r' t' m') :: s) r t m
    end
  | App (e0, e1, _) ->
    let f_e1_xs = f7 e1 xs in
    let f_e0_xs = f7 e0 xs in
    f_e1_xs vs
      (fun (v1 :: s1) (VEnv (vs) :: r1) t1 m1 ->
          f_e0_xs vs
            (fun (v0 :: VArg (v1) :: s0) r0 t0 m0 ->
                apply7 v0 v1 c s0 r0 t0 m0
            ) (VArg (v1) :: s1) r1 t1 m1
      ) s (VEnv (vs) :: r) t m
  | Shift (x, e) ->
    f7 e (x :: xs) (VContS (c, s, r, t) :: vs) idc [] [] TNil m
  | Control (x, e) ->
    f7 e (x :: xs) (VContC (c, s, r, t) :: vs) idc [] [] TNil m
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
  | Reset (e) -> f7 e xs vs idc [] [] TNil (MCons ((c, s, r, t), m))

(* apply7 : v -> v -> c -> s -> r -> t -> m -> v *)
and apply7 v0 v1 c s r t m = match v0 with
    VFun (f) -> f c (v1 :: s) r t m
  | VContS (c', s', r', t') -> c' (v1 :: s') r' t' (MCons ((c, s, r, t), m))
  | VContC (c', s', r', t') ->
    c' (v1 :: s') r' (apnd t' (cons (fun v t m -> c (v :: s) r t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

and apply_op7 op v0 v1 c s1 r1 t1 m1 = match (v0, v1) with
    (VNum (n0), VNum (n1)) ->
    begin match op with
      Plus -> c (VNum (n0 + n1) :: s1) r1 t1 m1
    | Minus -> c (VNum (n0 - n1) :: s1) r1 t1 m1
    | Times -> c (VNum (n0 * n1) :: s1) r1 t1 m1
    | Divide ->
      if n1 = 0 then failwith "Division by zero"
      else c (VNum (n0 / n1) :: s1) r1 t1 m1
    end
  | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                   ^ " are not numbers")

(* f : e -> v *)
let f expr = f7 expr [] [] idc [] [] TNil MNil
