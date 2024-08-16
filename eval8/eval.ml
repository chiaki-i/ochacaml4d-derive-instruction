open Syntax
open Value

(* Interpreter using combinators factored as instructions : eval8 *)

(* initial continuation : s -> t -> m -> v *)
let idc v s t m = match s with
    [] ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> c v s t m
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
let (>>) i0 i1 = fun vs c a s t m ->
  i0 vs (fun v' s' t' m' -> i1 vs c v' s' t' m') a s t m

(* (>>>) : i -> i' -> i' *)
let (>>>) i0 i1 = fun vs vs_out c a s t m ->
  i0 vs (fun v' s' t' m' -> i1 vs_out vs c v' s' t' m') a s t m

(* (>>>>) : i' -> i -> i *)
let (>>>>) i0 i1 = fun vs c a s t m ->
  i0 vs [] (fun v' s' t' m' -> i1 vs c v' s' t' m') a s t m

(* push : i *)
let push = fun vs c a s t m -> c a (a :: s) t m

(* apply8 : v -> v -> v list -> c -> s -> t -> m -> v *)
let apply8 v0 v1 v2s c s t m = match v0 with
    VFun (f) -> f v1 v2s c s t m
  | VContS (c', s', t') -> c' v1 s' t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    c' v1 s' (apnd t' (cons (fun v t m -> c v s t m) t)) m
  | _ -> failwith (to_string v0
                    ^ " is not a function; it can not be applied.")

(* return : c -> v -> s -> t -> m -> v *)
(* TODO: >>> で接続する *)
let ret c v (VEnv (vs_out) :: s) t m = match vs_out with
    [] -> c v s t m
  | first :: rest -> apply8 v first rest c s t m

(* num : int -> i *)
let num n = fun vs c a s t m -> c (VNum (n)) s t m

(* num' : int -> i' *)
let num' n = fun vs vs_out c a s t m ->
  ret c (VNum (n)) (VEnv (vs_out) :: s) t m

(* access : int -> i *)
let access n = fun vs c a s t m -> c (List.nth vs n) s t m

(* access' : int -> i' *)
let access' n = fun vs vs_out c a s t m ->
  ret c (List.nth vs n) (VEnv (vs_out) :: s) t m

(* cur : i -> i *)
let cur i = fun vs c a s t m ->
    let vfun = VFun (fun v vs_out c' s' t' m' ->
            i (v :: vs) vs_out c' v s' t' m'
        ) in
    c vfun s t m

(* grab : i' -> i' *)
let grab i' = fun vs vs_out c a s t m ->
  begin match vs_out with
          [] -> c (VFun (fun v vs_out c' s' t' m' ->
                i' (v :: vs) vs_out c' v s' t' m')) s t m (* adding vs_out, change f5 to f5t *)
      | first :: rest -> i' (first :: vs) rest c a s t m
  end

(* operation : op -> i *)
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

(* operation : op -> i' *)
let operation' op = fun vs vs_out c v0 s t m -> match s with
    v1 :: s ->
    begin match (v0, v1) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> ret c (VNum (n0 + n1)) (VEnv (vs_out) :: s) t m
          | Minus -> ret c (VNum (n0 - n1)) (VEnv (vs_out) :: s) t m
          | Times -> ret c (VNum (n0 * n1)) (VEnv (vs_out) :: s) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else ret c (VNum (n0 / n1)) (VEnv (vs_out) :: s) t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                       ^ " are not numbers")
    end
  | _ -> failwith "stack error: op"

(* pushmark : i *)
(* (特に f8 において) vs_out が空であるという情報を積む *)
let pushmark = fun vs c a s t m -> c (VEnv ([])) s t m

(* mark : i' *)
(* pushmark ではなく普通の vs_out を積む *)
let mark = fun vs vs_out c a s t m -> c (VEnv vs_out) s t m

(* apply : i *)
(* acc に v0 が積まれた状態で実行される *)
let apply = fun vs c v0 s t m -> match s with
  v1 :: VEnv (v2s) :: s -> apply8 v0 v1 v2s c s t m

(* appterm : i *)
let appterm = fun vs vs_out c v0 s t m -> match s with
  v1 :: VEnv (v2s) :: s -> apply8 v0 v1 v2s c s t m

(* aux : i *)
let aux = fun v2s c v1 s t m ->
  match s with VEnv (v2s) :: s ->
    c (VEnv (v1 :: v2s)) s t m

(* aux : i' *)
let aux' = fun v2s vs_out c v1 s t m ->
  match s with VEnv (v2s) :: s ->
    c (VEnv (v1 :: v2s)) s t m

(* f8 : e -> string list -> i *)
let rec f8 e xs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.offset x xs)
  | Op (e0, op, e1) ->
    f8 e1 xs >> push >> f8 e0 xs >> operation (op)
  | Fun (x, e) -> cur (f8t e (x :: xs))
  | App (e0, e1, e2s) ->
    (* pushmark inserted by f8s *)
    (f8s e2s xs) >> push >> (f8 e1 xs) >> push >> (f8 e0 xs) >> apply
  | _ -> failwith "not implemented"
  (* | Shift (x, e) -> shift (f8 e (x :: xs)) *)
  (* | Control (x, e) -> control (f8 e (x :: xs)) *)
  (* | Shift0 (x, e) -> shift0 (f8 e (x :: xs)) *)
  (* | Control0 (x, e) -> control0 (f8 e (x :: xs)) *)
  (* | Reset (e) -> reset (f8 e xs) *)

(* f8s : e -> string list -> env -> i *)
and f8s es xs = match es with
    [] -> pushmark
  | first :: rest ->
    (f8s rest xs) >> push >> (f8 first xs) >> aux

(* f8t : e -> string list -> v list -> i' *)
and f8t e xs = match e with
    Num (n) -> num' n
  | Var (x) -> access' (Env.offset x xs)
  | Op (e0, op, e1) ->
    (f8 e1 xs) >> push >> (f8 e0 xs) >>> operation' (op)
  | Fun (x, e) -> grab (f8t e (x :: xs))
  | App (e0, e1, e2s) ->
    (f8st e2s xs) >>>> push >> (f8 e1 xs) >> push >> (f8 e0 xs) >>> appterm
  | _ -> failwith "not implemented"
  (* | Shift (x, e) -> shift (f8 e (x :: xs)) *)
  (* | Control (x, e) -> control (f8 e (x :: xs)) *)
  (* | Shift0 (x, e) -> shift0 (f8 e (x :: xs)) *)
  (* | Control0 (x, e) -> control0 (f8 e (x :: xs)) *)
  (* | Reset (e) -> reset (f8 e xs) *)

and f8st es xs = match es with
    [] -> mark
  | first :: rest ->
    (f8st rest xs) >>>> push >> (f8 first xs) >>> aux'

(* f : e -> v *)
let f expr = f8 expr [] [] idc (VNum 7) [] TNil MNil

(*
(* shift : i -> i *)
let shift i = fun c s t m -> match s with
    VEnv (vs) :: s -> i idc (VEnv (VContS (c, s, t) :: vs) :: []) TNil m
  | _ -> failwith "stack error: shift"

(* control : i -> i *)
let control i = fun c s t m -> match s with
    VEnv (vs) :: s -> i idc (VEnv (VContC (c, s, t) :: vs) :: []) TNil m
  | _ -> failwith "stack error: control"

(* shift0 : i -> i *)
let shift0 i = fun c s t m -> match s with
    VEnv (vs) :: s ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        i c0 (VEnv (VContS (c, s, t) :: vs) :: s0) t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | _ -> failwith "stack error: shift0"

(* control0 : i -> i *)
let control0 i = fun c s t m -> match s with
    VEnv (vs) :: s ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        i c0 (VEnv (VContC (c, s, t) :: vs) :: s0) t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | _ -> failwith "stack error: control0"

(* reset : i -> i *)
let reset i = fun c s t m -> match s with
    VEnv (vs) :: s -> i idc (VEnv (vs) :: []) TNil (MCons ((c, s, t), m))
  | _ -> failwith "stack error: reset"
*)