open Syntax
open Value

(* Delinearized interpreter : eval5 (with return stack) *)
(* cs * c -> cs *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c5 : c -> v -> s -> r -> t -> m -> v *)
let rec run_c5 c v s r t m = match (c, s, r) with
    (C0, [], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, r, t), m) -> run_c5 c v s r t m
        end
      | Trail (h) -> h v TNil m
    end
  | (CApp0 (c), VArgs (v2s) :: s, r) -> apply5s v v2s c s r t m
  | (CAppS0 (cs), VArgs (v2s) :: s, r) -> run_c5s cs (v :: v2s) s r t m
  | (COp0 (op, c), v0 :: s, r) ->
    begin match (v, v0) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c5 c (VNum (n0 + n1)) s r t m
          | Minus -> run_c5 c (VNum (n0 - n1)) s r t m
          | Times -> run_c5 c (VNum (n0 * n1)) s r t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c5 c (VNum (n0 / n1)) s r t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
  | (COp1 (e0, xs, op, vs, c), s, r) ->
    f5 e0 xs vs (COp0 (op, c)) (v :: s) r t m
  | (CRet (C0), s, c' :: r') ->
    run_c5 c' v s r' t m
  | _ -> failwith "stack or cont error"

(* run_c5s : cs -> v list -> s -> r -> t -> m -> v *)
and run_c5s cs v2s s r t m = match cs with
    CApp2 (e0, xs, vs, c) ->
    f5 e0 xs vs (CApp0 (c)) (VArgs (v2s) :: s) r t m
  | CAppS1 (e, xs, vs, cs) ->
    f5 e xs vs (CAppS0 (cs)) (VArgs (v2s) :: s) r t m

(* f5 : e -> string list -> v list -> c -> s -> r -> t -> m -> v *)
and f5 e xs vs c s r t m = match e with
    Num (n) -> run_c5 c (VNum (n)) s r t m
  | Var (x) -> run_c5 c (List.nth vs (Env.offset x xs)) s r t m
  | Op (e0, op, e1) -> f5 e1 xs vs (COp1 (e0, xs, op, vs, c)) s r t m
  | Fun (x, e) ->
    begin match (c, s, r) with
      (CApp0 (c'), VArgs (v1 :: v2s) :: s', r') -> (* Grab *)
             f5 e (x :: xs) (v1 :: vs) (CApp0 (c')) (VArgs (v2s) :: s') r' t m
    | _ -> run_c5 c (VFun (fun v1 _ s' (c' :: r') t' m' ->
             f5 e (x :: xs) (v1 :: vs) (CRet (C0)) s' (c' :: r') t' m')) s r t m
    end
  | App (e0, e2s) ->
    f5s e2s xs vs (CApp2 (e0, xs, vs, c)) s r t m
  | Shift (x, e) -> f5 e (x :: xs) (VContS (c, s, r, t) :: vs) C0 [] [] TNil m
  | Control (x, e) -> f5 e (x :: xs) (VContC (c, s, r, t) :: vs) C0 [] [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        f5 e (x :: xs) (VContS (c, s, r, t) :: vs) c0 s0 r0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        f5 e (x :: xs) (VContC (c, s, r, t) :: vs) c0 s0 r0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f5 e xs vs C0 [] [] TNil (MCons ((c, s, r, t), m))

(* f5s : e list -> string list ->
         v list -> cs -> s -> r -> t -> m -> v list *)
and f5s e2s xs vs cs s r t m = match e2s with
    [] -> run_c5s cs [] s r t m
  | e :: e2s ->
    f5s e2s xs vs (CAppS1 (e, xs, vs, cs)) s r t m

(* apply5 : v -> v -> c -> s -> r -> t -> m -> v *)
and apply5 v0 v1 c s r t m = match v0 with
    VFun (f) -> f v1 C0 (* dummy *) s (c :: r) t m
  | VContS (c', s', r', t') -> run_c5 c' v1 s' r' t' (MCons ((c, s, r, t), m))
  | VContC (c', s', r', t') ->
    run_c5 c' v1 s' r' (apnd t' (cons (fun v t m -> run_c5 c v s r t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply5s : v -> v list -> c -> s -> r -> t -> m -> v *)
and apply5s v0 v2s c s r t m = match v2s with
    [] -> run_c5 c v0 s r t m
  | v1 :: v2s -> apply5 v0 v1 (CApp0 (c)) (VArgs (v2s) :: s) r t m

(* f : e -> v *)
let f expr = f5 expr [] [] C0 [] [] TNil MNil
