open Syntax
open Value

(* push : v -> s -> s *)
(* 引数スタック s の中の、先頭の引数列に値を追加する *)
let push v s = match s with
    [] -> failwith "s must be ((_ :: _) :: _), not []"
  | fst :: rest -> (v :: fst) :: rest

(* pushmark : i *)
let pushmark = fun vs c s t m -> c ([] :: s) t m

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = fun vs c -> i0 vs (i1 vs c)

(* num : int -> i *)
let num n = fun vs c s t m -> c (push (VNum (n)) s) t m

(* access : int -> i *)
let access n = fun vs c s t m -> c (push (List.nth vs n) s) t m

(* operation : op -> i *)
let operation op = fun vs c ((v :: v0 :: rest) :: s) t m ->
  begin match (v, v0) with
      (VNum (n0), VNum (n1)) ->
      begin match op with
          Plus -> c ((VNum (n0 + n1) :: rest) :: s) t m
        | Minus -> c ((VNum (n0 - n1) :: rest) :: s) t m
        | Times -> c ((VNum (n0 * n1) :: rest) :: s) t m
        | Divide ->
          if n1 = 0 then failwith "Division by zero"
          else c ((VNum (n0 / n1) :: rest) :: s) t m
      end
    | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
  end

(* cur : i -> i *)
let cur i = fun vs c s t m ->
  c (push (VFun (fun c' ((v1 :: v2s) :: s') t' m' ->
    i (v1 :: vs) c' (v2s :: s') t' m')) s) t m

(* grab: i -> i *)
let grab i = fun vs c s t m ->
  begin match s with
    [] :: s -> c (push (VFun (fun c' ((v1 :: v2s) :: s') t' m' ->
      i (v1 :: vs) c' (v2s :: s') t' m')) s) t m
  | (v1 :: v2s') :: s -> i (v1 :: vs) c (v2s' :: s) t m
  | _ -> failwith "grab: stack is empty"
  end

(* app : v -> v -> c -> s -> t -> m -> v *)
let rec app v0 v1 c s t m =
  let app_c ((v :: v2s) :: s) t m = app_s v c (v2s :: s) t m in
  match v0 with
    VFun (f) -> f c (push v1 s) t m
  | VContS (c', s', t') ->
    c' (push v1 s') t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    c' (push v1 s') (apnd t' (cons (fun v t m -> app_s v c s t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can't be applied.")

(* app_s : v -> v list -> c -> s -> t -> m -> v *)
and app_s v0 c (v2s :: s) t m = match v2s with
    [] -> c (push v0 s) t m
  | v1 :: v2s -> app v0 v1 c (v2s :: s) t m

(* initial continuation : s -> t -> m -> v *)
and idc s t m = match s with
    (v :: []) :: s ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c0, s, t), m) ->
            let app_c0 ((v :: v2s) :: s) t m = app_s v c0 (v2s :: s) t m in
            app_c0 (push v s) t m
        end
      | Trail (h) -> h v TNil m
    end
  | _ -> failwith "idc: stack error"

(* apply : i *)
let apply = fun vs c ((v :: v1 :: v2s) :: s) t m ->
  app v v1 c (v2s :: s) t m

(* skip : i *)
let skip = fun vs c (v2s' :: s) t m -> c (v2s' :: s) t m

(* return : i *)
let return = fun vs c ((v :: v2s) :: s) t m ->
  app_s v c (v2s :: s) t m

(* shift : i -> i *)
let shift i = fun vs c s t m ->
  i (VContS (c, s, t) :: vs) idc [[]] TNil m

(* control : i -> i *)
let control i = fun vs c s t m ->
  i (VContC (c, s, t) :: vs) idc [[]] TNil m

(* shift0 : i -> i *)
let shift0 i = fun vs c s t m -> match m with
    MCons ((c0, s0, t0), m0) ->
    i (VContS (c, s, t) :: vs) c0 s0 t0 m0
  | _ -> failwith "shift0 is used without enclosing reset"

(* control0 : i -> i *)
let control0 i = fun vs c s t m -> match m with
    MCons ((c0, s0, t0), m0) ->
    i (VContC (c, s, t) :: vs) c0 s0 t0 m0
  | _ -> failwith "control0 is used without enclosing reset"

(* reset : i -> i *)
(* MCons の第 2 要素は「reset の結果に適用すべき引数列」を先頭フレームに持つ。
   m から pop する側（idc）が app_c0 を作って必ずフレームを 1 つ消費するので、
   非末尾の reset（f 側、適用すべき引数がない）は空フレームを 1 つ用意する必要がある。
   末尾の reset（f_t 側）は適用すべき引数が s の先頭にすでにあるので、s のまま。
   この空フレームを「reset が内包する」か「f / f_t が pushmark として出す」かは
   設計の選択で、両者は同じだが、ここでは前者を採用している。

   案 A（採用）: reset が内包する。f / f_t の規則が短くなる
       let reset i = fun vs c s t m -> i vs idc [[]] TNil (MCons ((c, [] :: s, t), m))
       f   : | Reset (e) -> reset (f e xs)
       f_t : | Reset (e) -> reset (f e xs) >> return

   案 B: f / f_t が pushmark を出す。空フレームを積むことがコード上に見える
       let reset i = fun vs c s t m -> i vs idc [[]] TNil (MCons ((c, s, t), m))
       f   : | Reset (e) -> pushmark >> reset (f e xs)
       f_t : | Reset (e) -> pushmark >> reset (f e xs) >> return *)
let reset i = fun vs c s t m ->
  i vs idc [[]] TNil (MCons ((c, [] :: s, t), m))

(* f : definitional interpreter *)
(* f : e -> string list -> v list -> c -> s -> t -> m -> v *)
let rec f e xs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.offset x xs)
  | Op (e0, op, e1) ->
    f e1 xs >> f e0 xs >> operation op
  | Fun (x, e) -> cur (f_t e (x :: xs))
  | App (e0, e2s) ->
    f_s e2s xs >> f e0 xs >> apply
  | Shift (x, e) -> shift (f e (x :: xs))
  | Control (x, e) -> control (f e (x :: xs))
  | Shift0 (x, e) -> shift0 (f_t e (x :: xs))
  | Control0 (x, e) -> control0 (f_t e (x :: xs))
  (* 案 B: | Reset (e) -> pushmark >> reset (f e xs) *)
  | Reset (e) -> reset (f e xs)

(* f_t : e -> string list -> i *)
and f_t e xs = match e with
    Num (n) -> num n >> return
  | Var (x) -> access (Env.offset x xs) >> return
  | Op (e0, op, e1) ->
    f e1 xs >> f e0 xs >> operation op >> return
  | Fun (x, e) -> grab (f_t e (x :: xs))
  | App (e0, e2s) -> f_st e2s xs >> f e0 xs >> apply
  | Shift (x, e) -> shift (f e (x :: xs)) >> return
  | Control (x, e) -> control (f e (x :: xs)) >> return
  | Shift0 (x, e) -> shift0 (f_t e (x :: xs)) >> return
  | Control0 (x, e) -> control0 (f_t e (x :: xs)) >> return
  (* 案 B: | Reset (e) -> pushmark >> reset (f e xs) >> return *)
  | Reset (e) -> reset (f e xs) >> return

(* f_s : e list -> string list -> i *)
and f_s e2s xs = match e2s with
    [] -> pushmark
  | e :: e2s -> f_s e2s xs >> f e xs

(* f_st : e list -> string list -> i *)
and f_st e2s xs = match e2s with
    [] -> skip
  | e :: e2s -> f_st e2s xs >> f e xs

(* f_init : e -> v *)
let f_init expr = f expr [] [] idc [[]] TNil MNil
