open Syntax
open Value

(* push : v -> s -> s *)
(* 引数スタック s の中の、先頭の引数列に値を追加する *)
let push v s = match s with
    [] -> failwith "s must be ((_ :: _) :: _)"
  | fst :: rest -> (v :: fst) :: rest

(* pushmark : s -> s *)
let pushmark s = [] :: s

(* initial continuation : s -> t -> m -> v *)
let idc s t m = match s with (v :: []) :: s ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> c (push v s) t m
        end
      | Trail (h) -> h v TNil m
    end

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* f : definitional interpreter *)
(* f : e -> string list -> v list -> c -> s -> t -> m -> v *)
let rec f e xs vs c s t m =
  match e with
    Num (n) -> c (push (VNum (n)) s) t m
  | Var (x) -> c (push (List.nth vs (Env.offset x xs)) s) t m
  | Op (e0, op, e1) ->
    f e1 xs vs (fun s t m ->
      f e0 xs vs (fun ((v :: v0 :: rest) :: s) t m ->
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
      ) s t m) s t m
  | Fun (x, e) ->
    c (push (VFun (fun c' ((v1 :: v2s) :: s') t' m' ->
      f_t e (x :: xs) (v1 :: vs) c' (v2s :: s') t' m')) s) t m
  | App (e0, e2s) ->
    f_s e2s xs vs (fun s t m ->
      f e0 xs vs (fun ((v :: v1 :: v2s) :: s) t m ->
        app v v1 c (v2s :: s) t m
        ) s t m) s t m
  | Shift (x, e) -> f e (x :: xs) (VContS (c, s, t) :: vs) idc [[]] TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (c, s, t) :: vs) idc [[]] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
          f e (x :: xs) (VContS (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
          f e (x :: xs) (VContC (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc [[]] TNil (MCons ((c, s, t), m))

(* f_t : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f_t e xs vs c s t m =
  let app_c ((v :: v2s) :: s) t m = app_s v c (v2s :: s) t m in
  match e with
    Num (n) -> app_c (push (VNum (n)) s) t m
  | Var (x) -> app_c (push (List.nth vs (Env.offset x xs)) s) t m
  | Op (e0, op, e1) ->
    f e1 xs vs (fun s t m ->
      f e0 xs vs (fun ((v :: v0 :: rest) :: s) t m ->
        begin match (v, v0) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> app_c ((VNum (n0 + n1) :: rest) :: s) t m
              | Minus -> app_c ((VNum (n0 - n1) :: rest) :: s) t m
              | Times -> app_c ((VNum (n0 * n1) :: rest) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else app_c ((VNum (n0 / n1) :: rest) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
        end
      ) s t m) s t m
  | Fun (x, e) ->
    begin match s with
        [] :: s -> c (push (VFun (fun c' ((v1 :: v2s) :: s') t' m' ->
          f_t e (x :: xs) (v1 :: vs) c' (v2s :: s') t' m')) s) t m
      | (v1 :: v2s') :: s -> f_t e (x :: xs) (v1 :: vs) c (v2s' :: s) t m
    end
  | App (e0, e2s) ->
    begin match s with v2s' :: s ->
      f_st e2s xs vs (fun s t m ->
        f e0 xs vs (fun ((v :: v1 :: v2s) :: s) t m ->
          app v v1 c (v2s :: s) t m) s t m)
        (v2s' :: s) t m
    end
  | Shift (x, e) -> f e (x :: xs) (VContS (app_c, s, t) :: vs) idc [[]] TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (app_c, s, t) :: vs) idc [[]] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
          f e (x :: xs) (VContS (app_c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
          f e (x :: xs) (VContC (app_c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc [[]] TNil (MCons ((app_c, s, t), m))

(* f_s : e list -> string list -> c -> s -> t -> m -> v list *)
and f_s e2s xs vs c s t m = match e2s with
    [] -> c (pushmark s) t m
  | e :: e2s ->
    f_s e2s xs vs (fun s t m ->
      f e xs vs (fun ((v :: v2s) :: s) t m ->
        c ((v :: v2s) :: s) t m)
      s t m) s t m

(* f_st : e list -> string list -> c -> s -> t -> m -> v list *)
and f_st e2s xs vs c (v2s' :: s) t m = match e2s with
    [] -> c (v2s' :: s) t m
  | e :: e2s ->
    f_st e2s xs vs (fun s t m ->
      f e xs vs (fun ((v :: v2s) :: s) t m ->
        c ((v :: v2s) :: s) t m)
      s t m) (v2s' :: s) t m

(* app : v -> v -> c -> s -> t -> m -> v *)
and app v0 v1 c s t m =
  let app_c ((v :: v2s) :: s) t m = app_s v c (v2s :: s) t m in
  match v0 with
    VFun (f) -> f c (push v1 s) t m
  | VContS (c', s', t') ->
    c' (push v1 s') t' (MCons ((app_c, s, t), m))
  | VContC (c', s', t') ->
    c' (push v1 s') (apnd t' (cons (fun v t m -> app_s v c s t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can't be applied.")

(* app_s : v -> v list -> c -> s -> t -> m -> v *)
and app_s v0 c (v2s :: s) t m = match v2s with
    [] -> c (push v0 s) t m
  | v1 :: v2s -> app v0 v1 c (v2s :: s) t m

(* f_init : e -> v *)
let f_init expr = f expr [] [] idc [[]] TNil MNil
