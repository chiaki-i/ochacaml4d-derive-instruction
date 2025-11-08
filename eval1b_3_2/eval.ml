open Syntax
open Value

(* Definitional interpreter for (λ-calculus with 4 delimited continuation operations : eval1s *)

(* initial continuation : v -> t -> m -> v *)
let idc v t m = match t with
    TNil ->
    begin match m with
        MNil -> v
      | MCons ((c, t), m) -> c v t m
    end
  | Trail (h) -> h v TNil m

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* f : definitional interpreter *)
(* f : e -> string list -> v list -> c -> t -> m -> v *)
let rec f e xs vs c t m =
  match e with
    Num (n) -> c (VNum (n)) t m
  | Var (x) -> c (List.nth vs (Env.off_set x xs)) t m
  | Op (e0, op, e1) ->
    f e1 xs vs (fun v1 t0 m0 ->
        f e0 xs vs (fun v0 t1 m1 ->
            begin match (v0, v1) with
                (VNum (n0), VNum (n1)) ->
                begin match op with
                    Plus -> c (VNum (n0 + n1)) t1 m1
                  | Minus -> c (VNum (n0 - n1)) t1 m1
                  | Times -> c (VNum (n0 * n1)) t1 m1
                  | Divide ->
                    if n1 = 0 then failwith "Division by zero"
                    else c (VNum (n0 / n1)) t1 m1
                end
              | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                               ^ " are not numbers")
            end) t0 m0) t m
  | Fun (x, e) ->
    c (VFun (fun v1 v2s' c' t' m' ->
              f_t e (x :: xs) (v1 :: vs) v2s' c' t' m')) t m
  | App (e0, e2s) ->
    f_s e2s xs vs (fun v2s t2 m2 ->
      f e0 xs vs (fun v0 t0 m0 ->
        app_s v0 v2s c t0 m0) t2 m2) t m
  | Shift (x, e) -> f e (x :: xs) (VContS (c, t) :: vs) idc TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) ->
          f e (x :: xs) (VContS (c, t) :: vs) c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) ->
          f e (x :: xs) (VContC (c, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc TNil (MCons ((c, t), m))

(* f_t : e -> string list -> v list -> v list -> c -> t -> m -> v *)
and f_t e xs vs v2s' c t m =
  let app_c = fun v t m -> app_s v v2s' c t m in
  match e with
    Num (n) -> app_c (VNum (n)) t m
  | Var (x) -> app_c (List.nth vs (Env.off_set x xs)) t m
  | Op (e0, op, e1) ->
    f e1 xs vs (fun v1 t0 m0 ->
        f e0 xs vs (fun v0 t1 m1 ->
            begin match (v0, v1) with
                (VNum (n0), VNum (n1)) ->
                begin match op with
                    Plus -> app_c (VNum (n0 + n1)) t1 m1
                  | Minus -> app_c (VNum (n0 - n1)) t1 m1
                  | Times -> app_c (VNum (n0 * n1)) t1 m1
                  | Divide ->
                    if n1 = 0 then failwith "Division by zero"
                    else app_c (VNum (n0 / n1)) t1 m1
                end
              | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                               ^ " are not numbers")
            end) t0 m0) t m
  | Fun (x, e) ->
    app_c (VFun (fun v1 v2s' c' t' m' ->
              f_t e (x :: xs) (v1 :: vs) v2s' c' t' m')) t m
  | App (e0, e2s) ->
    (* f_st e0 e2s xs vs v2s' c t m *)
    f_st e2s xs vs v2s' (fun v2s t2 m2 -> (* 本当はこうなってほしい *)
      f e0 xs vs (fun v0 t0 m0 ->
        app_s v0 v2s c t0 m0) t2 m2) t m
  | Shift (x, e) -> f e (x :: xs) (VContS (app_c, t) :: vs) idc TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (app_c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) ->
          f e (x :: xs) (VContS (app_c, t) :: vs) c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) ->
          f e (x :: xs) (VContC (app_c, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc TNil (MCons ((app_c, t), m))

(* f_s : e list -> string list -> v list -> c -> t -> m -> v list *)
and f_s e2s xs vs c t m = match e2s with
    [] -> c [] t m
  | e :: e2s ->
    f_s e2s xs vs (fun v2s t2 m2 ->
      f e xs vs (fun v1 t1 m1 ->
        c (v1 :: v2s) t1 m1) t2 m2) t m

(* f_st : e list -> string list -> v list -> v list -> c -> t -> m -> v list *)
(* 本当はこうなってほしい *)
and f_st e2s xs vs v2s' c t m = match e2s with
    [] -> c v2s' t m
  | e :: e2s ->
    f_st e2s xs vs v2s' (fun v2s t2 m2 ->
      f e xs vs (fun v1 t1 m1 ->
        c (v1 :: v2s) t1 m1) t2 m2) t m

(* and f_st e0 e2s xs vs v2s' c t m =
  let app_c = fun v2s t2 m2 ->
    f e0 xs vs (fun v0 t0 m0 ->
      app_s v0 v2s (fun v t m -> app_s v v2s' c t m) t0 m0) t2 m2 in
  match e2s with
    [] ->
    (* app_c [] t m *) (* eval1b_3_1 original *)
    (* (fun v2s t2 m2 ->
      f e0 xs vs (fun v0 t0 m0 ->
        app_s v0 v2s (fun v t m -> app_s v v2s' c t m) t0 m0) t2 m2) [] t m *)
    (* f e0 xs vs (fun v0 t0 m0 ->
      app_s v0 [] (fun v t m -> app_s v v2s' c t m) t0 m0) t m *)
    (* f e0 xs vs (fun v0 t0 m0 -> c v0 t0 m0) t m *)
    f e0 xs vs c t m
  | e :: e2s ->
    (* f_s e2s xs vs (fun v2s t2 m2 ->
      f e xs vs (fun v1 t1 m1 ->
        app_c (v1 :: v2s) t1 m1) t2 m2) t m *) (* eval1b_3_1 original *)
    (* f_s e2s xs vs (fun v2s t2 m2 ->
      f e xs vs (fun v1 t1 m1 ->
        (fun v2s t2 m2 ->
          f e0 xs vs (fun v0 t0 m0 ->
            app_s v0 v2s (fun v t m -> app_s v v2s' c t m) t0 m0) t2 m2)
        (v1 :: v2s) t1 m1) t2 m2) t m *) (* app_c を単に代入しただけ *)
    (* f_s e2s xs vs (fun v2s t2 m2 ->
      f e xs vs (fun v1 t1 m1 ->
        f e0 xs vs (fun v0 t0 m0 ->
          app_s v0 (v1 :: v2s) (fun v t m -> app_s v v2s' c t m) t0 m0) t1 m1)
      t2 m2) t m *) (* (v1 :: v2s) t1 m1 を fun 文に代入する*)
    (* f_s e2s xs vs (fun v2s t2 m2 ->
      f e xs vs (fun v1 t1 m1 ->
        f e0 xs vs (fun v0 t0 m0 ->
          app v0 v1 v2s (fun v t m -> app_s v v2s' c t m) t0 m0) t1 m1)
      t2 m2) t m *) (* fun 文を簡約して app_s の (v1 :: v2s) であるとわかる *)
    f_s e2s xs vs (fun v2s t2 m2 ->
      f e xs vs (fun v1 t1 m1 ->
        f e0 xs vs (fun v0 t0 m0 ->
          app v0 v1 (v2s @ v2s') c t0 m0) t1 m1)
      t2 m2) t m
    (* 恣意的な append… これが appterm を意味するが、
    結局 v2s と v2s' を明示的に扱わないといけないので
    VEmpty を用いた実装につながらない *) *)

(* app : v -> v -> v list -> c -> t -> m -> v *)
and app v0 v1 v2s' c t m =
  let app_c = fun v t m -> app_s v v2s' c t m in
  match v0 with
    VFun (f) -> f v1 v2s' c t m
  | VContS (c', t') -> c' v1 t' (MCons ((app_c, t), m))
  | VContC (c', t') -> c' v1 (apnd t' (cons app_c t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* app_s : v -> v list -> c -> t -> m -> v *)
and app_s v0 v2s c t m = match v2s with
    [] -> c v0 t m
  | v1 :: v2s -> app v0 v1 v2s c t m

(* f_init : e -> v *)
let f_init expr = f expr [] [] idc TNil MNil
