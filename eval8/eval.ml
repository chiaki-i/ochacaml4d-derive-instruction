open Syntax
open Value

(* Interpreter using combinators factored as instructions : eval8 *)

(* initial continuation : s -> t -> m -> v *)
let idc v s_a s_r t m = match s_a with
    [] ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s_a, s_r, t), m) -> c v s_a s_r t m
        end
      | Trail (h) -> h v TNil m
    end
  | _ -> failwith "stack error: idc"

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* (>>) : i' -> i' -> i' *)
let (>>) i0 i1 = fun vs vs_out c a s_a s_r t m ->
  i0 vs vs_out (fun v' s_a' s_r' t' m' -> i1 vs vs_out c v' s_a' s_r' t' m') a s_a s_r t m

(* push : i' *)
let push = fun vs vs_out c a s_a s_r t m -> c a (a :: s_a) s_r t m

(* apply8 : v -> v -> v list -> c -> s -> t -> m -> v *)
let apply8 v0 v1 v2s c s_a s_r t m = match v0 with
    VFun (f) -> f v1 v2s c s_a s_r t m
  | VContS (c', s_a', s_r', t') -> c' v1 s_a' s_r' t' (MCons ((c, s_a, s_r, t), m))
  | VContC (c', s_a', s_r', t') ->
    c' v1 s_a' s_r' (apnd t' (cons (fun v t m -> c v s_a s_r t m) t)) m
  | _ -> failwith (to_string v0
                    ^ " is not a function; it cannot be applied.")

(* return : i' -> i' *)
let return = fun vs vs_out c a s_a s_r t m ->
  match vs_out with (* TODO: change vs_out to s_a / s_r *)
      VEmpty :: [] -> c a s_a s_r t m
    | first :: rest -> apply8 a first rest c s_a s_r t m
    | [] -> failwith "return error"

(* num : int -> i' *)
let num n = fun vs vs_out c a s_a s_r t m -> c (VNum (n)) s_a s_r t m

(* access : int -> i' *)
let access n = fun vs vs_out c a s_a s_r t m -> c (List.nth vs n) s_a s_r t m

(* cur : i' -> i' *)
let cur i = fun vs vs_out c a s_a s_r t m ->
    let vfun = VFun (fun v vs_out c' s_a' s_r' t' m' ->
            i (v :: vs) vs_out c' v s_a' s_r' t' m'
        ) in
    c vfun s_a s_r t m

(* grab : i' -> i' *)
(* vs_out が空かどうかによって次の instruction を実行するか決定する *)
(* そのため grab >> (f8 e xs) とは書けない *)
let grab i' = fun vs vs_out c a s_a s_r t m ->
  begin match vs_out with (* TODO: change vs_out to s_a / s_r *)
        [] ->
          c (VFun (fun v vs_out c' s_a' s_r' t' m' ->
            i' (v :: vs) vs_out c' v s_a' s_r' t' m')) s_a s_r t m
      | first :: rest -> i' (first :: vs) rest c a s_a s_r t m
  end

(* operation : op -> i' *)
let operation op = fun vs vs_out c v0 s_a s_r t m -> match s_a with
    v1 :: s_a ->
    begin match (v0, v1) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> c (VNum (n0 + n1)) s_a s_r t m
          | Minus -> c (VNum (n0 - n1)) s_a s_r t m
          | Times -> c (VNum (n0 * n1)) s_a s_r t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else c (VNum (n0 / n1)) s_a s_r t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                       ^ " are not numbers")
    end
  | _ -> failwith "stack error: op"

(* pushmark : i' *)
(* (特に f8 において) vs_out が空であるという情報を積む *)
let pushmark = fun vs vs_out c a s_a s_r t m -> c (VEnv [VEmpty]) s_a [VEmpty] t m

(* mark : i' *)
(* これ、return の 1つ目のパターン？*)
(* pushmark ではなく普通の vs_out を積む *)
let skip = fun vs vs_out c a s_a s_r t m -> c (VEnv vs_out) s_a s_r t m (* List.hd s_r にすべき？*)

(* apply : i' *)
(* acc に v0 が積まれた状態で実行される *)
let apply = fun vs vs_out c v0 s_a s_r t m -> match s_a with
  v1 :: VEnv (v2s) :: s_a -> apply8 v0 v1 v2s c s_a s_r t m

(* appterm : i' *)
let appterm = fun vs vs_out c v0 s_a s_r t m -> match s_a with
  v1 :: VEnv (v2s) :: s_a -> apply8 v0 v1 v2s c s_a s_r t m

(* aux : i' *)
let aux = fun v2s vs_out c v1 s_a s_r t m ->
  match s_a with VEnv (v2s) :: s_a ->
    c (VEnv (v1 :: v2s)) s_a s_r t m

(* shift : i' -> i' *)
let shift i = fun vs vs_out c a s_a s_r t m ->
  i (VContS (c, s_a, s_r, t) :: vs) vs_out idc a [] [] TNil m

(* control : i' -> i' *)
let control i = fun vs vs_out c a s_a s_r t m ->
  i (VContC (c, s_a, s_r, t) :: vs) vs_out idc a [] [] TNil m

(* shift0 : i' -> i' *)
let shift0 i = fun vs vs_out c a s_a s_r t m -> match m with
    MCons ((c0, s0_a, s0_r, t0), m0) ->
    i (VContS (c, s_a, s_r, t) :: vs) vs_out c0 a s0_a s0_r t0 m0
  | _ -> failwith "shift0 is used without enclosing reset"

(* control0 : i' -> i' *)
let control0 i = fun vs vs_out c a s_a s_r t m -> match m with
    MCons ((c0, s0_a, s0_r, t0), m0) ->
    i (VContC (c, s_a, s_r, t) :: vs) vs_out c0 a s0_a s0_r t0 m0
  | _ -> failwith "control0 is used without enclosing reset"

(* reset : i' -> i' *)
let reset i = fun vs vs_out c a s_a s_r t m ->
  i vs vs_out idc a [] [] TNil (MCons ((c, s_a, s_r, t), m))

(* f8 : e -> string list -> i' *)
let rec f8 e xs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.offset x xs)
  | Op (e0, op, e1) ->
    f8 e1 xs >> push >> f8 e0 xs >> operation (op)
  | Fun (x, e) -> cur (f8t e (x :: xs))
  | App (e0, e1, e2s) ->
    (* pushmark inserted by f8s *)
    (f8s e2s xs) >> push >> (f8 e1 xs) >> push >> (f8 e0 xs) >> apply
  | Shift (x, e) -> shift (f8 e (x :: xs))
  | Control (x, e) -> control (f8 e (x :: xs))
  | Shift0 (x, e) -> shift0 (f8 e (x :: xs))
  | Control0 (x, e) -> control0 (f8 e (x :: xs))
  | Reset (e) -> reset (f8 e xs)

(* f8s : e -> string list -> env -> i *)
and f8s es xs = match es with
    [] -> pushmark
  | first :: rest ->
    (f8s rest xs) >> push >> (f8 first xs) >> aux

(* f8t : e -> string list -> v list -> i' *)
and f8t e xs = match e with
    Num (n) -> num n >> return
  | Var (x) -> access (Env.offset x xs) >> return
  | Op (e0, op, e1) ->
    (f8 e1 xs) >> push >> (f8 e0 xs) >> operation (op) >> return
  | Fun (x, e) -> grab (f8t e (x :: xs))
  | App (e0, e1, e2s) ->
    (f8st e2s xs) >> push >> (f8 e1 xs) >> push >> (f8 e0 xs) >> appterm
  | Shift (x, e) -> shift (f8 e (x :: xs))
  | Control (x, e) -> control (f8 e (x :: xs))
  | Shift0 (x, e) -> shift0 (f8 e (x :: xs))
  | Control0 (x, e) -> control0 (f8 e (x :: xs))
  | Reset (e) -> reset (f8 e xs)

and f8st es xs = match es with
    [] -> skip
  | first :: rest ->
    (f8st rest xs) >> push >> (f8 first xs) >> aux

(* f : e -> v *)
let f expr = f8 expr [] [] [] idc (VNum 7) [] [] TNil MNil
