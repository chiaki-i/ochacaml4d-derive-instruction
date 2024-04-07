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
  | CApp0 (v1, v2s, c) -> apply2 v v1 v2s c t m
  | CApp1 (e0, xs, vs, v2s, c) -> (* vs, v2s are dynamic data *)
    f2 e0 xs vs (CApp0 (v, v2s, c)) t m
  | CAppS0 (v2s, cs) -> runs_c2 cs (v :: v2s) t m
  | CApply (first, rest, c) -> apply2 v first rest c t m
  | COp0 (e1, xs, vs, op, c) -> f2 e1 xs vs (COp1 (v, op, c)) t m
  | COp1 (v0, op, c) ->
    begin match (v0, v) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c2 c (VNum (n0 + n1)) t m
          | Minus -> run_c2 c (VNum (n0 - n1)) t m
          | Times -> run_c2 c (VNum (n0 * n1)) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c2 c (VNum (n0 / n1)) t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
  | _ -> failwith "run_c2: unexpected continuation"
(* runs_c2 : c -> v list -> t -> m -> v *)
(* cs receives v list instead of v *)
and runs_c2 cs v2s t m = match cs with
    CApp2 (e0, e1, xs, vs, c) ->
    f2 e1 xs vs (CApp1 (e0, xs, vs, v2s, c)) t m
  | CAppS1 (first, xs, vs, cs) ->
    f2 first xs vs (CAppS0 (v2s, cs)) t m
  | _ -> failwith "runs_c2: unexpected continuation"

(* f2 : e -> string list -> v list -> c -> t -> m -> v *)
and f2 e xs vs c t m = match e with
    Num (n) -> run_c2 c (VNum (n)) t m
  | Var (x) -> run_c2 c (List.nth vs (Env.offset x xs)) t m
  | Op (e0, op, e1) -> f2 e0 xs vs (COp0 (e1, xs, vs, op, c)) t m
  | Fun (x, e) ->
    run_c2 c (VFun (fun v c' t' m' -> f2 e (x :: xs) (v :: vs) c' t' m')) t m
  | App (e0, e1, e2s) ->
    f2s e2s xs vs (CApp2 (e0, e1, xs, vs, c)) t m
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
(* f2s : e list -> string list -> v list -> c -> t -> m -> c *)
(* In f2s, c receives v list *)
and f2s e2s xs vs cs t m = match e2s with
    [] -> runs_c2 cs [] t m
  | first :: rest ->
    f2s rest xs vs (CAppS1 (first, xs, vs, cs)) t m
(* apply2 : v -> v -> v list -> c -> t -> m -> v *)
and apply2 v0 v1 v2s c t m = match v2s with
    [] -> app2 v0 v1 c t m
  | first :: rest ->
    app2 v0 v1 (CApply (first, rest, c)) t m
(* app2 : v -> v -> c -> t -> m -> v *)
and app2 v0 v1 c t m = match v0 with
    VFun (f) -> f v1 c t m
  | VContS (c', t') -> run_c2 c' v1 t' (MCons ((c, t), m))
  | VContC (c', t') ->
    run_c2 c' v1 (apnd t' (cons (fun v t m -> run_c2 c v t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* f : e -> v *)
let f expr = f2 expr [] [] idc TNil MNil
