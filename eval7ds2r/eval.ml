open Syntax
open Value

(* Defunctionalized interpreter with values passed via stack : eval7d w r.s.*)
(* Add superfluous v list to CApp0, CAppS0, and COp0 *)

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
  | (CApp0 (vs, c), v :: VArgs (v2s) :: s, r) -> app_s v v2s vs c s r t m
  | (CApp2 (e0, xs, vs, c), VArgs (v2s) :: s, r) ->
    f e0 xs vs (CApp0 (vs, c)) (VArgs (v2s) :: s) r t m
  | (CAppS0 (vs, c), v :: VArgs (v2s) :: s, r) ->
    run_c7 c (VArgs (v :: v2s) :: s) r t m
  | (CAppS1 (e, xs, vs, c), VArgs (v2s) :: s, r) ->
    f e xs vs (CAppS0 (vs, c)) (VArgs (v2s) :: s) r t m
  | (COp0 (op, vs, c), v :: v0 :: s, r) ->
    begin match (v, v0) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c7 c (VNum (n0 + n1) :: s) r t m
          | Minus -> run_c7 c (VNum (n0 - n1) :: s) r t m
          | Times -> run_c7 c (VNum (n0 * n1) :: s) r t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c7 c (VNum (n0 / n1) :: s) r t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
  | (COp1 (e0, xs, op, vs, c), v :: s, r) ->
    f e0 xs vs (COp0 (op, vs, c)) (v :: s) r t m
  | _ -> failwith "stack or cont error"

(* f : e -> string list -> v list -> c -> s -> r -> t -> m -> v *)
and f e xs vs c s r t m = match e with
    Num (n) -> run_c7 c (VNum (n) :: s) r t m
  | Var (x) -> run_c7 c (List.nth vs (Env.off_set x xs) :: s) r t m
  | Op (e0, op, e1) -> f e1 xs vs (COp1 (e0, xs, op, vs, c)) s r t m
  | Fun (x, e) ->
    begin match (c, s, r) with
      (CApp0 (vs', c'), VArgs (v1 :: v2s) :: s', r') -> (* Grab *)
             f e (x :: xs) (v1 :: vs)
                  (CApp0 (vs', c')) (VArgs (v2s) :: s') r' t m
    | _ -> run_c7 c (VFun (fun c' (v1 :: s') r' t' m' ->
             f e (x :: xs) (v1 :: vs) c' s' r' t' m') :: s) r t m
    end
  | App (e0, e2s) ->
    f_s e2s xs vs (CApp2 (e0, xs, vs, c)) s r t m
  | Shift (x, e) -> f e (x :: xs) (VContS (c, s, r, t) :: vs) C0 [] [] TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (c, s, r, t) :: vs) C0 [] [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        f e (x :: xs) (VContS (c, s, r, t) :: vs) c0 s0 r0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        f e (x :: xs) (VContC (c, s, r, t) :: vs) c0 s0 r0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs C0 [] [] TNil (MCons ((c, s, r, t), m))

(* f_s : e list -> string list -> v list -> c -> s -> r -> t -> m -> v list *)
and f_s e2s xs vs c s r t m = match e2s with
    [] -> run_c7 c (VArgs ([]) :: s) r t m
  | e :: e2s ->
    f_s e2s xs vs (CAppS1 (e, xs, vs, c)) s r t m

(* app : v -> v -> c -> s -> r -> t -> m -> v *)
and app v0 v1 c s r t m = match v0 with
    VFun (f) -> f c (v1 :: s) r t m
  | VContS (c', s', r', t') ->
    run_c7 c' (v1 :: s') r' t' (MCons ((c, s, r, t), m))
  | VContC (c', s', r', t') ->
    run_c7 c' (v1 :: s') r'
           (apnd t' (cons (fun v t m -> run_c7 c (v :: s) r t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* app_s : v -> v list -> v list -> c -> s -> r -> t -> m -> v *)
and app_s v0 v2s vs c s r t m = match v2s with
    [] -> run_c7 c (v0 :: s) r t m
  | v1 :: v2s -> app v0 v1 (CApp0 (vs, c)) (VArgs (v2s) :: s) r t m

(* f_init : e -> v *)
let f_init expr = f expr [] [] C0 [] [] TNil MNil
