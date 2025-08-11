open Syntax
open Value

(* Definitional interpreter for λ-calculus with 4 delimited continuation operations
  with tail optimization : eval1st *)

(* initial continuation : v -> t -> m -> v *)
let idc v t m = match t with
    TNil ->
    begin match m with
        MNil -> v
      | MCons ((c, v2s, t), m) ->
        begin match v2s with
            [] -> c v t m
          | _ -> failwith "idc: unexpected v2s"
        end
    end
  | Trail (h) -> h v TNil m

(* cons : (v -> t -> m -> v) -> v list -> t -> t *)
let rec cons h v2s t =
  match t with
    TNil -> Trail (h)
  | Trail (h') ->
    Trail (fun v t' m -> (fun v t m -> apply1s v v2s h t m) v (cons h' v2s t') m)

(* apnd : t -> t -> t *)
and apnd t0 v2s t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h [] t1 (* ここで append すべき v2s は本当にからで良いのか *)

(* f1 : e -> string list -> v list -> c -> t -> m -> v *)
and f1 e xs vs c t m =
  match e with
    Num (n) -> c (VNum (n)) t m
  | Var (x) -> c (List.nth vs (Env.offset x xs)) t m
  | Op (e0, op, e1) ->
    f1 e1 xs vs (fun v1 t0 m0 ->
        f1 e0 xs vs (fun v0 t1 m1 ->
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
              f1t e (x :: xs) (v1 :: vs) v2s c' t' m')) t m
  | App (e0, e2s) ->
    f1s e2s xs vs (fun (v1 :: v2s) t2 m2 ->
      f1 e0 xs vs (fun v0 t0 m0 ->
        apply1 v0 v1 v2s c t0 m0) t2 m2) t m
  | Shift (x, e) ->
    (* f1 e (x :: xs) (VContS (c, t) :: vs) idc TNil m *) (* VContS - step1 *)
    (* f1 e (x :: xs) (VContS ((fun v v2s t (MCons ((c', t'), m'))-> apply1s v v2s c' t' m'), t) :: vs) idc TNil m *)
    (* 上は step2 のボツ案; これは c そのものを変更せねばならず影響範囲が大きすぎる *)
    (* begin match m with (* VContS - step2 採用案: v2s を MCons に積む *)
        MCons ((_, v2s', _), _) -> (* v2s を取り出して *)
        f1 e (x :: xs) (VContS ((fun v t' m' -> apply1s v v2s' c t' m'), t) :: vs) idc TNil m (* v2s を apply1s に渡す *)
      | MNil -> failwith "shift: unexpected m"
    end *)
    begin match m with
        MCons ((_, v2s', _), _) -> (* v2s を取り出して ← これは何を意味する？ *)
        (* v2s' が VContS と f1sr の中に複製されるが、どこかのタイミングでスタックに搭載できないか？ *)
        f1sr e (x :: xs) (VContS (c, t) :: vs) v2s' idc TNil m
      | MNil -> failwith "shift: unexpected m"
    end
  | Control (x, e) ->
    f1 e (x :: xs) (VContC (c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, v2s', t0), m0) ->
          f1sr e (x :: xs) (VContS (c, t) :: vs) v2s' c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
  end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          f1 e (x :: xs) (VContC (c, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f1 e xs vs idc TNil (MCons ((c, [], t), m))

(* f1t : e -> string list -> v list -> v list -> c -> t -> m -> v *)
and f1t e xs vs v2s c t m =
  let app_c = fun v0 t0 m0 -> apply1s v0 v2s c t0 m0 in
  match e with
    Num (n) -> app_c (VNum (n)) t m
  | Var (x) -> app_c (List.nth vs (Env.offset x xs)) t m
  | Op (e0, op, e1) ->
    f1 e1 xs vs (fun v1 t0 m0 ->
        f1 e0 xs vs (fun v0 t1 m1 ->
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
          f1t e (x :: xs) (v1 :: vs) v2s c' t' m')) t m
      | v1 :: v2s -> f1t e (x :: xs) (v1 :: vs) v2s c t m
    end
  | App (e0, e2s) ->
    f1s e2s xs vs (fun (v1 :: v2s) t2 m2 ->
      f1 e0 xs vs (fun v0 t0 m0 ->
        apply1 v0 v1 v2s app_c t0 m0) t2 m2) t m
  | Shift (x, e) ->
    (* f1 e (x :: xs) (VContS (app_c, t) :: vs) idc TNil m *)
    (* f1 e (x :: xs) (VContS ((fun v t' m' -> apply1s v v2s c t' m'), t) :: vs) idc TNil m *) (* VContS - step 2 *)
    f1sr e (x :: xs) (VContS (c, t) :: vs) v2s idc TNil m (* VContS - step 3 *)
  | Control (x, e) -> f1 e (x :: xs) (VContC (app_c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, _, t0), m0) ->
          f1sr e (x :: xs) (VContS (c, t) :: vs) v2s c0 t0 m0
          (* ↑ VContS - step 2: v2s' でも v2s でも結果同じなのでテストケース拡充した方が良いかも *)
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, _, t0), m0) ->
          f1 e (x :: xs) (VContC (app_c, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f1 e xs vs idc TNil (MCons ((app_c, [], t), m))

and f1sr e xs vs v2s c t m =
  let app_c = fun v0 t0 m0 -> apply1s v0 v2s c t0 m0 in
  match e with
    Num (n) -> app_c (VNum (n)) t m
  | Var (x) -> app_c (List.nth vs (Env.offset x xs)) t m
  | Op (e0, op, e1) ->
    f1 e1 xs vs (fun v1 t0 m0 ->
        f1 e0 xs vs (fun v0 t1 m1 ->
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
          f1t e (x :: xs) (v1 :: vs) v2s c' t' m')) t m
      | v1 :: v2s -> f1t e (x :: xs) (v1 :: vs) v2s c t m
    end
  | App (e0, e2s) ->
    f1s e2s xs vs (fun (v1 :: v2s) t2 m2 ->
      f1 e0 xs vs (fun v0 t0 m0 ->
        apply1 v0 v1 v2s app_c t0 m0) t2 m2) t m
  | Shift (x, e) ->
    (* f1 e (x :: xs) (VContS (app_c, t) :: vs) idc TNil m *)
    f1sr e (x :: xs) (VContS (c, t) :: vs) v2s idc TNil m (* VContS - step 2 *)
  | Control (x, e) -> f1 e (x :: xs) (VContC (app_c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, _, t0), m0) ->
          f1sr e (x :: xs) (VContS (c, t) :: vs) v2s c0 t0 m0
          (* ↑ VContS - step 2: v2s' でも v2s でも結果同じなのでテストケース拡充した方が良いかも *)
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, _, t0), m0) ->
          f1 e (x :: xs) (VContC (app_c, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f1 e xs vs idc TNil (MCons ((app_c, [], t), m))


(* f1s : e list -> string list -> v list -> c -> t -> m -> v list *)
and f1s e2s xs vs c t m = match e2s with
    [] -> c [] t m
  | e :: e2s ->
    f1s e2s xs vs (fun v2s t2 m2 ->
      f1 e xs vs (fun v1 t1 m1 ->
        c (v1 :: v2s) t1 m1) t2 m2) t m

(* apply1 : v -> v -> v list -> c -> t -> m -> v *)
and apply1 v0 v1 v2s c t m = match v0 with
    VFun (f) -> f v1 v2s c t m
  | VContS (c', t') ->
    (* c' v1 t' (MCons (((fun v t m -> apply1s v v2s c t m), t), m)) *) (* VContS - step1 *)
    c' v1 t' (MCons ((c, v2s, t), m)) (* MCons の v2s に実質的な中身を積んでいるのはここ *)
  | VContC (c', t') ->
    (* c' v1 (apnd t' (cons (fun v t m -> apply1s v v2s c t m) t)) m *) (* VContC - step 1: inline expansion *)
    c' v1 (apnd t' [] (cons c v2s t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply1s : v -> v list -> c -> t -> m -> v *)
and apply1s v0 v2s c t m = match v2s with
    [] -> c v0 t m
  | v1 :: v2s -> apply1 v0 v1 v2s c t m

(* f : e -> v *)
let f expr = f1 expr [] [] idc TNil MNil
