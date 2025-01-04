open Syntax
open Value

(* Defunctionalized interpreter with values passed via stack : eval7d w r.s.*)
(* Refunctionalize c'.  Derived from eval7ds3v *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c7 : c -> s -> r -> t -> m -> v *)
let rec run_c7 c s r t m = match (c, s, r) with
    (C0, v :: [], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, r, t), m) -> run_c7 c (v :: s) r t m
        end
      | Trail (h) -> h v TNil m
    end
  | (CSeq (c', c), (v :: s), rv :: r) ->
    c' rv c (v :: s) r t m

(* apply7 : v -> v -> c -> s -> r -> t -> m -> v *)
let apply7 v0 v1 c s r t m = match v0 with
    VFun (f) -> f C0 (* dummy *) (v1 :: s) (VK (c, r) :: []) t m
  | VContS (c', s', r', t') ->
    run_c7 c' (v1 :: s') r' t' (MCons ((c, s, r, t), m))
  | VContC (c', s', r', t') ->
    run_c7 c' (v1 :: s') r'
           (apnd t' (cons (fun v t m -> run_c7 c (v :: s) r t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply7s : v -> v list -> v list -> c -> s -> r -> t -> m -> v *)
let rec apply7s v0 v2s vs c s r t m = match v2s with
    [] -> run_c7 c (v0 :: s) r t m
  | v1 :: v2s ->
    apply7 v0 v1 (CSeq (apply, c)) (VArgs (v2s) :: s) (VS (vs) :: r) t m

(* apply : c' *)
and apply = fun (VS (vs)) c s r t m -> match s with
  v0 :: VArgs (v2s) :: s -> apply7s v0 v2s vs c s r t m

(* f7 : e -> string list -> v list -> c -> s -> r -> t -> m -> v *)
let rec f7 e xs vs c s r t m = match e with
    Num (n) -> run_c7 c (VNum (n) :: s) r t m
  | Var (x) -> run_c7 c (List.nth vs (Env.offset x xs) :: s) r t m
  | Op (e0, op, e1) ->
    f7 e1 xs vs (CSeq ((fun (VS (vs)) c (v :: s) r t m ->
      f7 e0 xs vs (CSeq ((fun (VS (vs)) c (v :: v0 :: s) r t m ->
        begin match (v, v0) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c7 c (VNum (n0 + n1) :: s) r t m
              | Minus -> run_c7 c (VNum (n0 - n1) :: s) r t m
              | Times -> run_c7 c (VNum (n0 * n1) :: s) r t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c7 c (VNum (n0 / n1) :: s) r t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v
                          ^ " are not numbers")
        end
      ), c)) (v :: s) (VS (vs) :: r) t m
    ), c)) s (VS (vs) :: r) t m
  | Fun (x, e) ->
    begin match (c, s, r) with
      (CSeq (i', c'), VArgs (v1 :: v2s) :: s', VS (vs') :: r')
             when i' == apply ->
             f7 e (x :: xs) (v1 :: vs) (* Grab *)
                  (CSeq (apply, c')) (VArgs (v2s) :: s')
                  (VS (vs') :: r') t m
    | _ -> run_c7 c (VFun (fun _ (v1 :: s') (VK (c', r') :: []) t' m' ->
             f7 e (x :: xs) (v1 :: vs) (CSeq ((fun (VS (vs)) c (v :: s)
                                                (VK (c', r') :: []) t m ->
               run_c7 c' (v :: s) r' t m
             ), C0)) s' (VS (vs) :: VK (c', r') :: []) t' m') :: s) r t m
    end
  | App (e0, e2s) ->
    f7s e2s xs vs (CSeq ((fun (VS (vs)) c (VArgs (v2s) :: s) r t m ->
      f7 e0 xs vs (CSeq ((fun (VS (vs)) c (v0 :: VArgs (v2s) :: s) r t m ->
        apply7s v0 v2s vs c s r t m)
        , c)) (VArgs (v2s) :: s) (VS (vs) :: r) t m
    ), c)) s (VS (vs) :: r) t m
  | Shift (x, e) -> f7 e (x :: xs) (VContS (c, s, r, t) :: vs) C0 [] [] TNil m
  | Control (x, e) -> f7 e (x :: xs) (VContC (c, s, r, t) :: vs) C0 [] [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        f7 e (x :: xs) (VContS (c, s, r, t) :: vs) c0 s0 r0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, r0, t0), m0) ->
        f7 e (x :: xs) (VContC (c, s, r, t) :: vs) c0 s0 r0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f7 e xs vs C0 [] [] TNil (MCons ((c, s, r, t), m))

(* f7s : e list -> string list -> v list -> c -> s -> r -> t -> m -> v list *)
and f7s e2s xs vs c s r t m = match e2s with
    [] -> run_c7 c (VArgs ([]) :: s) r t m
  | e :: e2s ->
    f7s e2s xs vs (CSeq ((fun (VS (vs)) c (VArgs (v2s) :: s) r t m ->
      f7 e xs vs (CSeq ((fun (VS (vs)) c (v :: VArgs (v2s) :: s) r t m ->
        run_c7 c (VArgs (v :: v2s) :: s) r t m
      ), c)) (VArgs (v2s) :: s) (VS (vs) :: r) t m
    ), c)) s (VS (vs) :: r) t m

(* f : e -> v *)
let f expr = f7 expr [] [] C0 [] [] TNil MNil
