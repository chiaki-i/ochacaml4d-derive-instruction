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

(* f : e -> string list -> v list -> c -> t -> m -> v *)
let rec f e xs vs c t m = match e with
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
    c (VFun (fun v1 v2s c' t' m' -> f_t e (x :: xs) (v1 :: vs) v2s c' t' m'))
      t m
  | App (e0, e1, e2s) ->
    f_s e2s xs vs (fun v2s t2 m2 ->
      f e1 xs vs (fun v1 t1 m1 ->
        f e0 xs vs (fun v0 t0 m0 ->
          app v0 v1 v2s c t0 m0) t1 m1) t2 m2) t m
  | Shift (x, e) -> f e (x :: xs) (VContS (c, t) :: vs) idc TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (c, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) -> f e (x :: xs) (VContS (c, t) :: vs) c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) -> f e (x :: xs) (VContC (c, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc TNil (MCons ((c, t), m))
and f_s e2s xs vs c t m = match e2s with
    [] -> c [] t m
  | first :: rest ->
    f_s rest xs vs (fun v2s t2 m2 ->
      f first xs vs (fun v1 t1 m1 ->
        c (v1 :: v2s) t1 m1) t2 m2) t m
and app1 v0 v1 c t m = match v0 with
    VFun (f) -> failwith "Cannot happen"
  | VContS (c', t') -> c' v1 t' (MCons ((c, t), m))
  | VContC (c', t') -> c' v1 (apnd t' (cons c t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")
and app v0 v1 v2s c t m = match v0 with
    VFun (f) -> f v1 v2s c t m
  | _ ->
  (* VContS/C �ξ��ϸŤ��ޤޡ������� VFun �Τ褦���ѹ����Ƥ������� *)
  app1 v0 v1
    (fun f t1 m1 ->
      begin match v2s with
          [] -> c f t1 m1
        | first :: rest ->
          app f first rest c t1 m1
      end
    ) t m

(* f_t : e -> string list -> v list -> v list -> c -> t -> m -> v *)
and f_t e xs vs v2s c t m =
  let ret v t m = match v2s with
      [] -> c v t m
    | v1 :: v2s -> app v v1 v2s c t m in
  match e with
    Num (n) -> ret (VNum (n)) t m
  | Var (x) -> ret (List.nth vs (Env.off_set x xs)) t m
  | Op (e0, op, e1) ->
    f e1 xs vs (fun v1 t0 m0 ->
        f e0 xs vs (fun v0 t1 m1 ->
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
    begin match v2s with
        [] -> c (VFun (fun v1 v2s c' t' m' ->
                        f_t e (x :: xs) (v1 :: vs) v2s c' t' m')) t m
      | v1 :: v2s -> f_t e (x :: xs) (v1 :: vs) v2s c t m
    end
  | App (e0, e1, e2s) ->
    f_s e2s xs vs (fun v2s t2 m2 ->
      f e1 xs vs (fun v1 t1 m1 ->
        f e0 xs vs (fun v0 t0 m0 ->
          app v0 v1 v2s ret t0 m0) t1 m1) t2 m2) t m
  | Shift (x, e) -> f e (x :: xs) (VContS (ret, t) :: vs) idc TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (ret, t) :: vs) idc TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) -> f e (x :: xs) (VContS (ret, t) :: vs) c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, t0), m0) -> f e (x :: xs) (VContC (ret, t) :: vs) c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc TNil (MCons ((ret, t), m))

(* f_init : e -> v *)
let f_init expr = f expr [] [] idc TNil MNil
