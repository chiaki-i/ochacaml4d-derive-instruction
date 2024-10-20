open Syntax
open Value

(* actual calculation *)
(* Definitional interpreter for (λ-calculus with 4 delimited continuation operations : eval1 *)

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

(* f1 : e -> string list -> v list -> c -> t -> m -> v *)
let rec f1 e xs vs c t m = match e with
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
    c (VFun (fun v1 vs_out c' t' m' -> f1t e (x :: xs) (v1 :: vs) vs_out c' t' m'))
      t m
  | App (e0, e1, e2s) ->
    f1s e2s xs vs (fun v2s t2 m2 ->
      f1 e1 xs vs (fun v1 t1 m1 ->
        f1 e0 xs vs (fun v0 t0 m0 ->
          apply1 v0 v1 v2s c t0 m0) t1 m1) t2 m2) t m
  | Shift (x, e) -> f1 e (x :: xs) (VContS (c, t) :: vs) idc TNil m
  | Control (x, e) -> f1 e (x :: xs) (VContC (c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) -> f1 e (x :: xs) (VContS (c, t) :: vs) c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) -> f1 e (x :: xs) (VContC (c, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f1 e xs vs idc TNil (MCons ((c, t), m))
and f1s e2s xs vs c t m = match e2s with
    [] -> c [] t m
  | first :: rest ->
    f1s rest xs vs (fun v2s t2 m2 ->
      f1 first xs vs (fun v1 t1 m1 ->
        c (v1 :: v2s) t1 m1) t2 m2) t m
and apply1 v0 v1 vs_out c t m = match v0 with
    VFun (f) -> f v1 vs_out c t m (* この vs_out は、f v1 という関数適用の外にある引数という意味での「クロージャの外側」*)
  | VContS (c', t') -> (* app1 をインライン展開しただけ *)
    let c =
      (fun f1 t1 m1 ->
      begin match vs_out with
          [] -> c f1 t1 m1
        | first :: rest ->
          apply1 f1 first rest c t1 m1
      end)
    in c' v1 t' (MCons ((c, t), m))
  | VContC (c', t') ->
    let c = (fun f1 t1 m1 ->
      begin match vs_out with
          [] -> c f1 t1 m1
        | first :: rest ->
          apply1 f1 first rest c t1 m1
      end)
    in
    c' v1 (apnd t' (cons c t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* f1t : e -> string list -> v list -> v list -> c -> t -> m -> v *)
and f1t e xs vs vs_out c t m =
  let ret v t m = match vs_out with
      [] -> c v t m
    | first :: rest -> apply1 v first rest c t m in
  match e with
    Num (n) -> ret (VNum (n)) t m
  | Var (x) -> ret (List.nth vs (Env.offset x xs)) t m
  | Op (e0, op, e1) ->
    f1 e1 xs vs (fun v1 t0 m0 ->
        f1 e0 xs vs (fun v0 t1 m1 ->
            begin match (v0, v1) with
                (VNum (n0), VNum (n1)) ->
                begin match op with
                    Plus -> ret (VNum (n0 + n1)) t1 m1
                  | Minus -> ret (VNum (n0 - n1)) t1 m1
                  | Times -> ret (VNum (n0 * n1)) t1 m1
                  | Divide ->
                    if n1 = 0 then failwith "Division by zero"
                    else ret (VNum (n0 / n1)) t1 m1
                end
              | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                               ^ " are not numbers")
            end) t0 m0) t m
  | Fun (x, e) ->
    begin match vs_out with
        [] -> c (VFun (fun v1 v2s c' t' m' ->
                        f1t e (x :: xs) (v1 :: vs) v2s c' t' m')) t m
      | first :: rest -> f1t e (x :: xs) (first :: vs) rest c t m (* Grab pops one arg from arg stack, pushes it onto the env *)
    end
  | App (e0, e1, e2s) ->
    f1st e2s xs vs vs_out (fun v2s t2 m2 -> (* Appterm *)
      f1 e1 xs vs (fun v1 t1 m1 ->
        f1 e0 xs vs (fun v0 t0 m0 ->
          apply1 v0 v1 v2s c t0 m0) t1 m1) t2 m2) t m
  | Shift (x, e) -> f1 e (x :: xs) (VContS (ret, t) :: vs) idc TNil m
  | Control (x, e) -> f1 e (x :: xs) (VContC (ret, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) -> f1 e (x :: xs) (VContS (ret, t) :: vs) c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) -> f1 e (x :: xs) (VContC (ret, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f1 e xs vs idc TNil (MCons ((ret, t), m))
and f1st e2s xs vs vs_out c t m = match e2s with
    [] -> c vs_out t m
  | first :: rest ->
    f1st rest xs vs vs_out (fun v2s t2 m2 ->
      f1 first xs vs (fun v1 t1 m1 ->
        c (v1 :: v2s) t1 m1) t2 m2) t m

(* f : e -> v *)
let f expr = f1 expr [] [] idc TNil MNil
