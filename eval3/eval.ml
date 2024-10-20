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
  | CApp0 (v1, v2s) :: c -> apply3 v v1 v2s c t m
  | CApp1 (e0, xs, vs, v2s) :: c ->
    f3 e0 xs vs (CApp0 (v, v2s) :: c) t m
  | CAppS0 (v2s) :: cs -> runs_c3 cs (v :: v2s) t m
  | CRet (vs_out) :: c ->
    begin match vs_out with
        [] -> run_c3 c v t m
      | first :: rest -> apply3 v first rest c t m
    end
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
  | COp2 (e0, xs, vs, vs_out, op) :: c -> f3 e0 xs vs (COp3 (v, vs_out, op) :: c) t m (* tail version *)
  | COp3 (v0, vs_out, op) :: c -> (* tail version *)
    begin match (v, v0) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c3 (CRet (vs_out) :: c) (VNum (n0 + n1)) t m
          | Minus -> run_c3 (CRet (vs_out) :: c) (VNum (n0 - n1)) t m
          | Times -> run_c3 (CRet (vs_out) :: c) (VNum (n0 * n1)) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c3 (CRet (vs_out) :: c) (VNum (n0 / n1)) t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
  | _ -> failwith "run_c3: unexpected continuation"
(* runs_c3 : c -> v list -> t -> m -> v *)
and runs_c3 c v t m = match c with
    CApp2 (e0, e1, xs, vs) :: c ->
    f3 e1 xs vs (CApp1 (e0, xs, vs, v) :: c) t m
  | CAppS1 (first, xs, vs) :: cs ->
    f3 first xs vs (CAppS0 (v) :: cs) t m
  | _ -> failwith "runs_c3: unexpected continuation"

(* f3 : e -> string list -> v list -> c -> t -> m -> v *)
and f3 e xs vs c t m = match e with
    Num (n) -> run_c3 c (VNum (n)) t m
  | Var (x) -> run_c3 c (List.nth vs (Env.offset x xs)) t m
  | Op (e0, op, e1) -> f3 e1 xs vs (COp0 (e0, xs, vs, op) :: c) t m
  | Fun (x, e) ->
    run_c3 c (VFun (fun v vs_out c' t' m' -> (* adding vs_out *)
      f3t e (x :: xs) (v :: vs) vs_out c' t' m')) t m (* change f3 to f3t *)
  | App (e0, e1, e2s) ->
    f3s e2s xs vs (CApp2 (e0, e1, xs, vs) :: c) t m
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
(* f3s : e list -> string list -> v list -> c -> t -> m -> v *)
and f3s e3s xs vs cs t m = match e3s with
    [] -> runs_c3 cs [] t m
  | first :: rest ->
    f3s rest xs vs (CAppS1 (first, xs, vs) :: cs) t m
(* apply3 : v -> v -> v list -> c -> t -> m -> v *)
and apply3 v0 v1 vs_out c t m = match v0 with
    VFun (f) -> f v1 vs_out c t m
  | VContS (c', t') -> run_c3 c' v1 t' (MCons ((c, t), m))
  | VContC (c', t') ->
    run_c3 c' v1 (apnd t' (cons (fun v t m -> run_c3 c v t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* f3t : e -> string list -> v list -> v list -> c -> t -> m -> v *)
and f3t e xs vs vs_out c t m =
  match e with
    Num (n) -> run_c3 (CRet (vs_out) :: c) (VNum (n)) t m
  | Var (x) -> run_c3 (CRet (vs_out) :: c) (List.nth vs (Env.offset x xs)) t m
  | Op (e0, op, e1) -> f3 e1 xs vs (COp2 (e0, xs, vs, vs_out, op) :: c) t m
  | Fun (x, e) ->
    begin match vs_out with
        [] -> run_c3 c (VFun (fun v1 vs_out c' t' m' ->
                f3t e (x :: xs) (v1 :: vs) vs_out c' t' m')) t m
      | first :: rest -> f3t e (x :: xs) (first :: vs) rest c t m
    end
  | App (e0, e1, e2s) ->
    f3st e2s xs vs vs_out (CApp2 (e0, e1, xs, vs) :: c) t m
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
and f3st e2s xs vs vs_out cs t m = match e2s with
    [] -> runs_c3 cs vs_out t m
  | first :: rest ->
    f3st rest xs vs vs_out (CAppS1 (first, xs, vs) :: cs) t m

(* f : e -> v *)
let f expr = f3 expr [] [] [] TNil MNil
