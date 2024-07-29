open Syntax
open Value

(* Stack-based interpreter : eval4 *)

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
  | (CApp0 :: c, v1 :: VEnv (v2s) :: s) ->
    apply4 v v1 v2s c s t m
  | (CApp1 (e0, xs) :: c, VEnv (v2s) :: VEnv (vs) :: s) ->
    f4 e0 xs vs (CApp0 :: c) (v :: VEnv (v2s) :: s) t m
  | (CAppS0 :: cs, VEnv (v2s) :: s) ->
    runs_c4 cs (v :: v2s) s t m
  | (CRet :: c, VEnv (vs_out) :: s) ->
    begin match vs_out with
        [] -> run_c4 c v s t m
      | first :: rest -> apply4 v first rest c s t m
    end
  | (COp0 (e0, xs, op) :: c, VEnv (vs) :: s) ->
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
  | (COp2 (e0, xs, op) :: c, VEnv (vs) :: VEnv (vs_out) :: s) -> (* tail version *)
    f4 e0 xs vs (COp3 (op) :: c) (v :: VEnv (vs_out) :: s) t m
  | (COp3 (op) :: c, v0 :: VEnv (vs_out) :: s) -> (* tail version *)
    begin match (v, v0) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c4 (CRet :: c) (VNum (n0 + n1)) (VEnv (vs_out) :: s) t m
          | Minus -> run_c4 (CRet :: c) (VNum (n0 - n1)) (VEnv (vs_out) :: s) t m
          | Times -> run_c4 (CRet :: c) (VNum (n0 * n1)) (VEnv (vs_out) :: s) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c4 (CRet :: c) (VNum (n0 / n1)) (VEnv (vs_out) :: s) t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
  | _ -> failwith "stack or cont error"
(* runs_c4: c -> v list -> s -> t -> m -> v *)
and runs_c4 c v s t m = match (c, s) with
    (CApp2 (e0, e1, xs) :: c, VEnv (vs) :: s) ->
    f4 e1 xs vs (CApp1 (e0, xs) :: c) (VEnv (v) :: VEnv (vs) :: s) t m
    (* ここでの v は e2 ... en の実行結果リスト *)
  | (CAppS1 (first, xs) :: cs, VEnv (vs) :: s) ->
    f4 first xs vs (CAppS0 :: cs) (VEnv (v) :: s) t m
  | _ -> failwith "runs_c4: unexpected continuation or stack"
(* apply4 : v -> v -> v list -> c -> s -> t -> m -> v *)
and apply4 v0 v1 vs_out c s t m = match v0 with
    VFun (f) -> f v1 vs_out c s t m
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
    f4 e1 xs vs (COp0 (e0, xs, op) :: c) (VEnv (vs) :: s) t m
  | Fun (x, e) ->
    run_c4 c (VFun (fun v vs_out c' s' t' m' ->
      f4t e (x :: xs) (v :: vs) vs_out c' s' t' m')) s t m (* adding vs_out, change f4 to f4t *)
  | App (e0, e1, e2s) ->
    f4s e2s xs vs (CApp2 (e0, e1, xs) :: c) (VEnv (vs) :: s) t m
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
(* f4s: e list -> string list -> v list -> c -> s -> t -> m *)
and f4s es xs vs c s t m = match es with
    [] -> runs_c4 c [] s t m
  | first :: rest ->
    f4s rest xs vs (CAppS1 (first, xs) :: c) (VEnv (vs) :: s) t m

and f4t e xs vs vs_out c s t m = match e with
    Num (n) -> run_c4 (CRet :: c) (VNum (n)) (VEnv (vs_out) :: s) t m
  | Var (x) -> run_c4 (CRet :: c) (List.nth vs (Env.offset x xs)) (VEnv (vs_out) :: s) t m
  | Op (e0, op, e1) ->
    f4 e1 xs vs (COp2 (e0, xs, op) :: c) (VEnv (vs) :: VEnv (vs_out) :: s) t m
  | Fun (x, e) ->
    begin match vs_out with
        [] -> run_c4 c (VFun (fun v vs_out c' s' t' m' ->
                f4t e (x :: xs) (v :: vs) vs_out c' s' t' m')) s t m (* adding vs_out, change f4 to f4t *)
      | first :: rest -> f4t e (x :: xs) (first :: vs) rest c s t m
    end
  | App (e0, e1, e2s) ->
    f4st e2s xs vs vs_out (CApp2 (e0, e1, xs) :: c) (VEnv (vs) :: s) t m
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
and f4st e2s xs vs vs_out cs s t m = match e2s with
    [] -> runs_c4 cs vs_out s t m
  | first :: rest ->
    f4st rest xs vs vs_out (CAppS1 (first, xs) :: cs) (VEnv (vs) :: s) t m


    (* f : e -> v *)
let f expr = f4 expr [] [] [] [] TNil MNil
