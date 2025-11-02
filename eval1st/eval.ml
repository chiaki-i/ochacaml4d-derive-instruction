open Syntax
open Value

(* Definitional interpreter for λ-calculus with 4 delimited continuation operations
  with tail optimization : eval1st *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (Append (h, h'))

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_h1 : h -> v -> t -> m -> v *)
let rec run_h1 h v t m = match h with
    Hold (c) -> c v t m
  | Append (h, h') -> run_h1 h v (cons h' t) m

(* initial continuation : v -> t -> m -> v *)
let rec idc v t m = match t with
    TNil ->
    begin match m with
        MNil -> v
      | MCons ((c0, v2s, t), m) ->
          let app_c0 = fun v0 t0 m0 -> app_s v0 v2s c0 t0 m0 in
          app_c0 v t m
    end
  | Trail (h) -> run_h1 h v TNil m

(* f : e -> string list -> v list -> c -> t -> m -> v *)
and f e xs vs c t m =
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
    c (VFun (fun v1 v2s c' t' m' ->
              f_t e (x :: xs) (v1 :: vs) v2s c' t' m')) t m
  | App (e0, e2s) ->
    f_s e2s xs vs (fun (v1 :: v2s) t2 m2 ->
      f e0 xs vs (fun v0 t0 m0 ->
        app v0 v1 v2s c t0 m0) t2 m2) t m
  | Shift (x, e) -> f e (x :: xs) (VContS (c, t) :: vs) idc TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          f_sr e (x :: xs) (VContS (c, t) :: vs) v2s c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          f_sr e (x :: xs) (VContC (c, t) :: vs) v2s c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc TNil (MCons ((c, [], t), m))

(* f_t : e -> string list -> v list -> v list -> c -> t -> m -> v *)
and f_t e xs vs v2s c t m =
  let app_c = fun v0 t0 m0 -> app_s v0 v2s c t0 m0 in
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
    begin match v2s with
        [] -> c (VFun (fun v1 v2s c' t' m' ->
          f_t e (x :: xs) (v1 :: vs) v2s c' t' m')) t m
          (* begin match e with
            App (e0, e2s) ->
              c (VFun (fun v1 v2s c' t' m' ->
                f_s e2s xs vs (fun (v1' :: v2s') t2 m2 ->
                  f e0 xs vs (fun v0 t0 m0 ->
                    app v0 v1' (v2s' @ v2s) c' t0 m0) t2 m2) t' m')) t m
            | _ -> c (VFun (fun v1 v2s c' t' m' ->
              f_t e (x :: xs) (v1 :: vs) v2s c' t' m')) t m
          end *)
      | v1 :: v2s -> f_t e (x :: xs) (v1 :: vs) v2s c t m
    end
    (* f_t の Fun の中で、e が関数適用だった場合 = 末尾呼び出しでの関数適用 = Appterm 相当 *)
    (* c (VFun (fun v1 v2s c' t' m' -> f_t (App (e0, e2s)) (x :: xs) (v1 :: vs) v2s c' t' m')) t m *)
    (* c (VFun (fun v1 v2s c' t' m' ->
        f_s e2s (x :: xs) (v1 :: vs) (fun (v1' :: v2s') t2 m2 ->
          f e0 (x :: xs) (v1 :: vs) (fun v0 t0 m0 ->
            app v0 v1' v2s' app_c t0 m0) t2 m2) t' m')) t m *)
    (* c (VFun (fun v1 v2s c' t' m' ->
        f_s e2s (x :: xs) (v1 :: vs) (fun (v1' :: v2s') t2 m2 ->
          f e0 (x :: xs) (v1 :: vs) (fun v0 t0 m0 ->
            app v0 v1' v2s' (fun v0 t0 m0 -> app_s v0 v2s c' t0 m0) t0 m0) t2 m2) t' m')) t m *)
  | App (e0, e2s) ->
    f_s e2s xs vs (fun (v1 :: v2s) t2 m2 ->
      f e0 xs vs (fun v0 t0 m0 ->
        app v0 v1 v2s app_c t0 m0) t2 m2) t m
      (* f_st (e0 :: e2s) xs vs (fun (v1 :: v2s') t2 m2 ->
        appterm1 v0 v1 v2s' v2s c t0 m0) t2 m2) t m *)
      (* appterm1 v0 v1 v2s' app_c t0 m0 *)
      (* appterm1' v0 v1 v2s' v2s c t0 m0 *)
      (* appterm1 v0 v1 (v2s' @ v2s) c t0 m0 *)
  | Shift (x, e) -> f e (x :: xs) (VContS (app_c, t) :: vs) idc TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (app_c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, v2s', t0), m0) ->
          f_sr e (x :: xs) (VContS (app_c, t) :: vs) v2s' c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, v2s', t0), m0) ->
          f_sr e (x :: xs) (VContC (app_c, t) :: vs) v2s' c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc TNil (MCons ((c, v2s, t), m))

(* f_sr : e -> string list -> v list -> v list -> c -> t -> m -> v *)
(* copied from f, change c to app_c0 *)
and f_sr e xs vs v2s c t m =
  let app_c0 = fun v0 t0 m0 -> app_s v0 v2s c t0 m0 in
  match e with
    Num (n) -> app_c0 (VNum (n)) t m
  | Var (x) -> app_c0 (List.nth vs (Env.off_set x xs)) t m
  | Op (e0, op, e1) ->
    f e1 xs vs (fun v1 t0 m0 ->
        f e0 xs vs (fun v0 t1 m1 ->
            begin match (v0, v1) with
                (VNum (n0), VNum (n1)) ->
                begin match op with
                    Plus -> app_c0 (VNum (n0 + n1)) t1 m1
                  | Minus -> app_c0 (VNum (n0 - n1)) t1 m1
                  | Times -> app_c0 (VNum (n0 * n1)) t1 m1
                  | Divide ->
                    if n1 = 0 then failwith "Division by zero"
                    else app_c0 (VNum (n0 / n1)) t1 m1
                end
              | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                               ^ " are not numbers")
            end) t0 m0) t m
  | Fun (x, e) ->
    app_c0 (VFun (fun v1 v2s c' t' m' ->
              f_t e (x :: xs) (v1 :: vs) v2s c' t' m')) t m
  | App (e0, e2s) ->
    f_s e2s xs vs (fun (v1 :: v2s) t2 m2 ->
      f e0 xs vs (fun v0 t0 m0 ->
        app v0 v1 v2s app_c0 t0 m0) t2 m2) t m
  | Shift (x, e) -> f e (x :: xs) (VContS (app_c0, t) :: vs) idc TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (app_c0, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          f_sr e (x :: xs) (VContS (app_c0, t) :: vs) v2s c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          f_sr e (x :: xs) (VContC (app_c0, t) :: vs) v2s c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  (* | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          let app_c0' = fun v0 t0 m0 -> app_s v0 v2s c0 t0 m0 in
          f e (x :: xs) (VContS (app_c0, t) :: vs) app_c0' t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          let app_c0' = fun v0 t0 m0 -> app_s v0 v2s c0 t0 m0 in
          f e (x :: xs) (VContC (app_c0, t) :: vs) app_c0' t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end *)
  | Reset (e) -> f e xs vs idc TNil (MCons ((app_c0, [], t), m))

(* f_s : e list -> string list -> v list -> c -> t -> m -> v list *)
and f_s e2s xs vs c t m = match e2s with
    [] -> c [] t m
  | e :: e2s ->
    f_s e2s xs vs (fun v2s t2 m2 ->
      f e xs vs (fun v1 t1 m1 ->
        c (v1 :: v2s) t1 m1) t2 m2) t m

(* appterm1 : v -> v -> v list -> c -> t -> m -> v *)
and appterm1 v0 v1 v2s' v2s c t m =
  let app_c = fun v0 t0 m0 -> app_s v0 v2s c t0 m0 in
  match v0 with
    VFun (f) -> f v1 (v2s' @ v2s) c t m
    (* v2s' = 現在評価中のクロージャの引数、v2s = return 先のクロージャの引数 *)
    (* VFun (f) -> f v1 v2s' app_c t m *) (* これと同じことを証明したい *)
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply1 *)
(* app : v -> v -> v list -> c -> t -> m -> v *)
and app v0 v1 v2s c t m = match v0 with
    VFun (f) -> f v1 v2s c t m
  | VContS (c', t') ->
    c' v1 t' (MCons ((c, v2s, t), m))
  | VContC (c', t') ->
    let app_c = fun v t m -> app_s v v2s c t m in
    c' v1 (apnd t' (cons (Hold (app_c)) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply1s *)
(* app_s : v -> v list -> c -> t -> m -> v *)
and app_s v0 v2s c t m = match v2s with
    [] -> c v0 t m
  | v1 :: v2s -> app v0 v1 v2s c t m

(* f_init : e -> v *)
let f_init expr = f expr [] [] idc TNil MNil
