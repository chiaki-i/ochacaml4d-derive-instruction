open Syntax
open Value

(* Interpreter using combinators factored as instructions : eval8 *)

(* initial continuation : s -> t -> m -> v *)
let idc s r t m = match (s, r) with
    (v :: [], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, r, t), m) -> c (v :: s) r t m
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

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = fun vs c s r t m ->
  i0 vs (fun s' r' t' m' -> i1 vs c s' r' t' m') s r t m

(* num : int -> i *)
let num n = fun vs c s r t m -> c (VNum (n) :: s) r t m

(* access : int -> i *)
let access n = fun vs c s r t m -> c (List.nth vs n :: s) r t m

(* operation : op -> i *)
let operation op = fun vs c s r t m -> match (s, r) with
    (v0 :: v1 :: s, r) ->
    begin match (v0, v1) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> c (VNum (n0 + n1) :: s) r t m
          | Minus -> c (VNum (n0 - n1) :: s) r t m
          | Times -> c (VNum (n0 * n1) :: s) r t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else c (VNum (n0 / n1) :: s) r t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                       ^ " are not numbers")
    end
  | _ -> failwith "stack error: op"

(* grab : i -> i *)
let grab i = fun vs c s r t m ->
  begin match (s, r) with
      (VArg (v1, c') :: s', r) -> (* Grab *)
        i (v1 :: vs) c' s' r t m
    | _ ->
        let vfun = VFun (fun c' s' r' t' m' ->
          begin match (s', r') with
            (v :: s', r') -> i (v :: vs) c' s' r' t' m'
          | _ -> failwith "stack error"
          end) in
        c (vfun :: s) r t m
  end

(* app : v -> v -> c -> s -> r -> t -> m -> v *)
let app v0 v1 c s r t m = match v0 with
    VFun (f) -> f c (v1 :: s) r t m
  | VContS (c', s', r', t') -> c' (v1 :: s') r' t' (MCons ((c, s, r, t), m))
  | VContC (c', s', r', t') ->
    c' (v1 :: s') r' (apnd t' (cons (fun v t m -> c (v :: s) r t m) t)) m
  | _ -> failwith (to_string v0
                    ^ " is not a function; it cannot be applied.")

(* app : i *)
let app = fun vs c s r t m -> match (s, r) with
  (v0 :: v1 :: s, r) -> app v0 v1 c s r t m

(* shift : i -> i *)
let shift i = fun vs c s r t m ->
  i (VContS (c, s, r, t) :: vs) idc [] [] TNil m

(* control : i -> i *)
let control i = fun vs c s r t m ->
  i (VContC (c, s, r, t) :: vs) idc [] [] TNil m

(* shift0 : i -> i *)
let shift0 i = fun vs c s r t m -> match m with
    MCons ((c0, s0, r0, t0), m0) ->
    i (VContS (c, s, r, t) :: vs) c0 s0 r0 t0 m0
  | _ -> failwith "shift0 is used without enclosing reset"

(* control0 : i -> i *)
let control0 i = fun vs c s r t m -> match m with
    MCons ((c0, s0, r0, t0), m0) ->
    i (VContC (c, s, r, t) :: vs) c0 s0 r0 t0 m0
  | _ -> failwith "control0 is used without enclosing reset"

(* reset : i -> i *)
let reset i = fun vs c s r t m ->
  i vs idc [] [] TNil (MCons ((c, s, r, t), m))

(* f : e -> string list -> i *)
let rec f e xs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.off_set x xs)
  | Op (e0, op, e1) ->
    f e1 xs >> f e0 xs >> operation (op)
  | Fun (x, e) -> grab (f e (x :: xs))
  | App (e0, e1, _) ->
    f e1 xs >> f e0 xs >> app
    (* vs を push/pop しなくてはならない *)
    (* あるいは env を（accumulator とともに？）引き回す *)
  | Shift (x, e) -> shift (f e (x :: xs))
  | Control (x, e) -> control (f e (x :: xs))
  | Shift0 (x, e) -> shift0 (f e (x :: xs))
  | Control0 (x, e) -> control0 (f e (x :: xs))
  | Reset (e) -> reset (f e xs)

(*
(* (>>) : i' -> i' -> i' *)
let (>>) i0 i1 = fun vs c a s t m ->
  i0 vs (fun v' s' t' m' -> i1 vs c v' s' t' m') a s t m

(* push : i' *)
let push = fun vs c a s t m -> c a (a :: s) t m

(* app : v -> v -> v list -> c -> s -> t -> m -> v *)
let app v0 v1 c (VArgs (v2s) :: s) t m = match v0 with
    VFun (f) -> f v1 v2s c s t m
  | VContS (c', s', t') -> c' v1 s' t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    c' v1 s' (apnd t' (cons (fun v t m -> c v s t m) t)) m
  | _ -> failwith (to_string v0
                    ^ " is not a function; it cannot be applied.")

(* return : i' -> i' *)
let return = fun vs c a (VArgs (vs_out) :: s) t m ->
  match vs_out with
      [] -> c a s t m
    | first :: rest -> app a first c (VArgs (rest) :: s) t m

(* num : int -> i' *)
let num n = fun vs c a s t m -> c (VNum (n)) s t m

(* access : int -> i' *)
let access n = fun vs c a s t m -> c (List.nth vs n) s t m

(* cur : i' -> i' *)
let cur i = fun vs c a s t m ->
    let vfun = VFun (fun v vs_out c' s' t' m' ->
            i (v :: vs) c' v (VArgs (vs_out) :: s') t' m'
        ) in
    c vfun s t m

(* grab : i' -> i' *)
(* vs_out が空かどうかによって次の instruction を実行するか決定する *)
(* そのため grab >> (f e xs) とは書けない *)
let grab i' = fun vs c a (VArgs (vs_out) :: s) t m ->
  begin match vs_out with
          [] -> c (VFun (fun v vs_out c' s' t' m' ->
                i' (v :: vs) c' v (VArgs (vs_out) :: s') t' m')) s t m
      | first :: rest -> i' (first :: vs) c a (VArgs (rest) :: s) t m
  end

(* operation : op -> i' *)
let operation op = fun vs c v0 s t m -> match s with
    v1 :: s ->
    begin match (v0, v1) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> c (VNum (n0 + n1)) s t m
          | Minus -> c (VNum (n0 - n1)) s t m
          | Times -> c (VNum (n0 * n1)) s t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else c (VNum (n0 / n1)) s t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                       ^ " are not numbers")
    end
  | _ -> failwith "stack error: op"

(* pushmark : i' *)
(* (特に f において) vs_out が空であるという情報を積む *)
let pushmark = fun vs c a s t m -> c (VEnv []) s t m

(* mark : i' *)
(* pushmark ではなく普通の vs_out を積む *)
let skip = fun vs c a s t m -> match s with (VArgs (vs_out) :: s) ->
    c (VEnv (vs_out)) s t m
  | _ -> failwith "stack error: skip"

(* app : i' *)
(* acc に v0 が積まれた状態で実行される *)
let app = fun vs c v0 s t m -> match s with
  v1 :: VEnv (v2s) :: s -> app v0 v1 c (VArgs (v2s) :: s) t m

(* appterm : i' *)
let appterm = fun vs c v0 s t m -> match s with
  v1 :: VEnv (v2s) :: s -> app v0 v1 c (VArgs (v2s) :: s) t m

(* aux : i' *)
let aux = fun v2s c v1 s t m ->
  match s with VEnv (v2s) :: s ->
    c (VEnv (v1 :: v2s)) s t m

(* shift : i' -> i' *)
let shift i = fun vs c a s t m ->
  i (VContS (c, s, t) :: vs) idc a [] TNil m

(* control : i' -> i' *)
let control i = fun vs c a s t m ->
  i (VContC (c, s, t) :: vs) idc a [] TNil m

(* shift0 : i' -> i' *)
let shift0 i = fun vs c a s t m -> match m with
    MCons ((c0, s0, t0), m0) ->
    i (VContS (c, s, t) :: vs) c0 a s0 t0 m0
  | _ -> failwith "shift0 is used without enclosing reset"

(* control0 : i' -> i' *)
let control0 i = fun vs c a s t m -> match m with
    MCons ((c0, s0, t0), m0) ->
    i (VContC (c, s, t) :: vs) c0 a s0 t0 m0
  | _ -> failwith "control0 is used without enclosing reset"

(* reset : i' -> i' *)
let reset i = fun vs c a s t m ->
  i vs idc a [] TNil (MCons ((c, s, t), m))

(* f : e -> string list -> i' *)
let rec f e xs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.off_set x xs)
  | Op (e0, op, e1) ->
    f e1 xs >> push >> f e0 xs >> operation (op)
  | Fun (x, e) -> cur (f_t e (x :: xs))
  | App (e0, e1, e2s) ->
    (* pushmark inserted by f_s *)
    (f_s e2s xs) >> push >> (f e1 xs) >> push >> (f e0 xs) >> app
  | Shift (x, e) -> shift (f e (x :: xs))
  | Control (x, e) -> control (f e (x :: xs))
  | Shift0 (x, e) -> shift0 (f e (x :: xs))
  | Control0 (x, e) -> control0 (f e (x :: xs))
  | Reset (e) -> reset (f e xs)

(* f_s : e -> string list -> env -> i *)
and f_s es xs = match es with
    [] -> pushmark
  | first :: rest ->
    (f_s rest xs) >> push >> (f first xs) >> aux

(* f_t : e -> string list -> i' *)
and f_t e xs = match e with
    Num (n) -> num n >> return
  | Var (x) -> access (Env.off_set x xs) >> return
  | Op (e0, op, e1) ->
    (f e1 xs) >> push >> (f e0 xs) >> operation (op) >> return
  | Fun (x, e) -> grab (f_t e (x :: xs))
  | App (e0, e1, e2s) ->
    (f_st e2s xs) >> push >> (f e1 xs) >> push >> (f e0 xs) >> appterm
  | Shift (x, e) -> shift (f e (x :: xs))
  | Control (x, e) -> control (f e (x :: xs))
  | Shift0 (x, e) -> shift0 (f e (x :: xs))
  | Control0 (x, e) -> control0 (f e (x :: xs))
  | Reset (e) -> reset (f e xs)

and f_st es xs = match es with
    [] -> skip
  | first :: rest ->
    (f_st rest xs) >> push >> (f first xs) >> aux
*)

(* f_init : e -> v *)
let f_init expr = f expr [] [] idc [] [] TNil MNil
