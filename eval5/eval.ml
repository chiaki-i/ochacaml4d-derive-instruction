open Syntax
open Value

(* Delinearized interpreter : eval5 *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c5 : c -> v -> s -> t -> m -> v *)
let rec run_c5 c v s t m = match (c, s) with
    (C0, []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c5 c v s t m
        end
      | Trail (h) -> h v TNil m
    end
  | (CApp0 (c), VEnv (v1 :: v2s) :: s) ->
    apply5 v v1 v2s c s t m
  | (CApp1 (e0, xs, c), VEnv (v2s) :: VEnv (vs) :: s) ->
    f5 e0 xs vs (CApp0 (c)) (VEnv (v :: v2s) :: s) t m
  | (CAppS0 (cs), VEnv (v2s) :: s) ->
    runs_c5 cs (v :: v2s) s t m
  | (CRet (c), VEnv (v2s) :: s) ->
    begin match v2s with
        [] -> run_c5 c v s t m
      | first :: rest -> apply5 v first rest c s t m
    end
  | (COp0 (e0, xs, op, c), VEnv (vs) :: s) ->
    f5 e0 xs vs (COp1 (op, c)) (v :: s) t m
  | (COp1 (op, c), v0 :: s) ->
    begin match (v, v0) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c5 c (VNum (n0 + n1)) s t m
          | Minus -> run_c5 c (VNum (n0 - n1)) s t m
          | Times -> run_c5 c (VNum (n0 * n1)) s t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c5 c (VNum (n0 / n1)) s t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
  | (COp2 (e0, xs, op, c), VEnv (vs) :: VEnv (v2s) :: s) -> (* tail version *)
    f5 e0 xs vs (COp3 (op, c)) (v :: VEnv (v2s) :: s) t m
  | (COp3 (op, c), v0 :: VEnv (v2s) :: s) -> (* tail version *)
    begin match (v, v0) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
          (* スタックの先頭には、CRet で使えるように 必ず VEnv (v2s) が乗っていることを明示している *)
          (* この v2s は「Closure の外側の引数情報」を指す *)
            Plus -> run_c5 (CRet (c)) (VNum (n0 + n1)) (VEnv (v2s) :: s) t m
          | Minus -> run_c5 (CRet (c)) (VNum (n0 - n1)) (VEnv (v2s) :: s) t m
          | Times -> run_c5 (CRet (c)) (VNum (n0 * n1)) (VEnv (v2s) :: s) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c5 (CRet (c)) (VNum (n0 / n1)) (VEnv (v2s) :: s) t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
    end
  | _ -> failwith "stack or cont error"
(* runs_c5: c -> v list -> s -> t -> m -> v *)
and runs_c5 c v s t m = match (c, s) with
    (CApp2 (e0, e1, xs, c), VEnv (vs) :: s) ->
    f5 e1 xs vs (CApp1 (e0, xs, c)) (VEnv (v) :: VEnv (vs) :: s) t m
  | (CAppS1 (first, xs, cs), VEnv (vs) :: s) ->
    f5 first xs vs (CAppS0 (cs)) (VEnv (v) :: s) t m
  | _ -> failwith "runs_c5: unexpected continuation or stack"
(* apply5 : v -> v -> v list -> c -> s -> t -> m -> v *)
and apply5 v0 v1 v2s c s t m = match v0 with
    VFun (f) -> f v1 v2s c s t m
  | VContS (c', s', t') -> run_c5 c' v1 s' t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    run_c5 c' v1 s' (apnd t' (cons (fun v t m -> run_c5 c v s t m) t)) m
  | _ -> failwith (to_string v0
                    ^ " is not a function; it can not be applied.")

(* f5 : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f5 e xs vs c s t m = match e with
    Num (n) -> run_c5 c (VNum (n)) s t m
  | Var (x) -> run_c5 c (List.nth vs (Env.offset x xs)) s t m
  | Op (e0, op, e1) ->
    f5 e1 xs vs (COp0 (e0, xs, op, c)) (VEnv (vs) :: s) t m
  | Fun (x, e) ->
    run_c5 c (VFun (fun v v2s c' s' t' m' -> (* add v2s *)
      f5t e (x :: xs) (v :: vs) v2s c' s' t' m')) s t m (* change f5 to f5t *)
  | App (e0, e1, e2s) ->
    f5s e2s xs vs (CApp2 (e0, e1, xs, c)) (VEnv (vs) :: s) t m
  | Shift (x, e) -> f5 e (x :: xs) (VContS (c, s, t) :: vs) C0 [] TNil m
  | Control (x, e) -> f5 e (x :: xs) (VContC (c, s, t) :: vs) C0 [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f5 e (x :: xs) (VContS (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f5 e (x :: xs) (VContC (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f5 e xs vs C0 [] TNil (MCons ((c, s, t), m))
(* f5s: e list -> string list -> v list -> s -> t -> m *)
and f5s es xs vs c s t m = match es with
    [] -> runs_c5 c [] s t m
  | first :: rest ->
    f5s rest xs vs (CAppS1 (first, xs, c)) (VEnv (vs) :: s) t m

and f5t e xs vs v2s c s t m = match e with
    Num (n) -> run_c5 (CRet (c)) (VNum (n)) (VEnv (v2s) :: s) t m
  | Var (x) -> run_c5 (CRet (c)) (List.nth vs (Env.offset x xs)) (VEnv (v2s) :: s) t m
  | Op (e0, op, e1) ->
    f5 e1 xs vs (COp2 (e0, xs, op, c)) (VEnv (vs) :: VEnv (v2s) :: s) t m
  | Fun (x, e) ->
    begin match v2s with
        [] -> run_c5 c (VFun (fun v v2s c' s' t' m' ->
                f5t e (x :: xs) (v :: vs) v2s c' s' t' m')) s t m (* add v2s, change f5 to f5t *)
      | v1 :: v2s -> f5t e (x :: xs) (v1 :: vs) v2s c s t m
    end
  | App (e0, e1, e2s) ->
    f5st e2s xs vs v2s (CApp2 (e0, e1, xs, c)) (VEnv (vs) :: s) t m (* change f5s to f5st *)
  | Shift (x, e) -> f5 e (x :: xs) (VContS (c, s, t) :: vs) C0 [] TNil m
  | Control (x, e) -> f5 e (x :: xs) (VContC (c, s, t) :: vs) C0 [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f5 e (x :: xs) (VContS (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f5 e (x :: xs) (VContC (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f5 e xs vs C0 [] TNil (MCons ((c, s, t), m))
and f5st e2s xs vs v2s cs s t m = match e2s with
    [] -> runs_c5 cs v2s s t m
  | first :: rest ->
    f5st rest xs vs v2s (CAppS1 (first, xs, cs)) (VEnv (vs) :: s) t m

(* f : e -> v *)
let f expr = f5 expr [] [] C0 [] TNil MNil
