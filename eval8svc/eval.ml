open Syntax
open Value

(* Interpreter using combinators factored as instructions : eval8sv *)
(* Derived from eval7ds4v *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c8 : c -> s -> r -> t -> m -> v *)
let rec run_c8 c s r t m = match (c, s, r) with
    (C0, v :: [], []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, r, t), m) -> run_c8 c (v :: s) r t m
        end
      | Trail (h) -> h v TNil m
    end
  | (CSeq (i1), (v :: s), rv :: r) ->
    i1 rv c (v :: s) r t m

(* (>>) : i -> i -> i *)
(* let (>>) i0 i1 = fun rv c s r t m ->
  i0 rv (CSeq (i1, c)) s (rv :: r) t m *)

(* (>>>) : i -> c -> c *)
let rec (>>>) i0 c1 = match c1 with
    C0 -> CSeq (i0)
  | CSeq (i1) -> CSeq (fun rv c s r t m -> i0 rv (i1 >>> c) s r t m)

(* (>>) : c -> c -> c *)
let (>>) c0 c1 = match c0 with
    C0 -> c1
  | CSeq (i0') -> i0' >>> c1

(* num : int -> i *)
let num n = fun (VS (vs)) c s r t m -> run_c8 c (VNum (n) :: s) r t m

(* access : int -> i *)
let access n = fun (VS (vs)) c s r t m -> run_c8 c (List.nth vs n :: s) r t m

(* operation : op -> i *)
let operation op = fun (VS (vs)) c s r t m -> match s with
    v0 :: v1 :: s ->
    begin match (v0, v1) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c8 c (VNum (n0 + n1) :: s) r t m
          | Minus -> run_c8 c (VNum (n0 - n1) :: s) r t m
          | Times -> run_c8 c (VNum (n0 * n1) :: s) r t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c8 c (VNum (n0 / n1) :: s) r t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                       ^ " are not numbers")
    end
  | _ -> failwith "stack error: op"

(* pushmark : i *)
let pushmark = fun (VS (vs)) c s r t m -> run_c8 c (VArgs ([]) :: s) r t m

(* push : i *)
let push = fun (VS (vs)) c (v :: VArgs (v2s) :: s) r t m ->
  run_c8 c (VArgs (v :: v2s) :: s) r t m

(* apply8 : v -> v -> c -> s -> r -> t -> m -> v *)
let apply8 v0 v1 c s r t m = match v0 with
    VFun (f) -> f C0 (* dummy *) (v1 :: s) (VK (c, r) :: []) t m
  | VContS (c', s', r', t') ->
    run_c8 c' (v1 :: s') r' t' (MCons ((c, s, r, t), m))
  | VContC (c', s', r', t') ->
    run_c8 c' (v1 :: s') r'
           (apnd t' (cons (fun v t m -> run_c8 c (v :: s) r t m) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can not be applied.")

(* apply8s : v -> v list -> v list -> c -> s -> r -> t -> m -> v *)
let rec apply8s v0 v2s vs c s r t m = match v2s with
    [] -> run_c8 c (v0 :: s) r t m
  | v1 :: v2s ->
    apply8 v0 v1 (apply >>> c)) (VArgs (v2s) :: s) (VS (vs) :: r) t m

(* apply : c' *)
and apply = fun (VS (vs)) c s r t m -> match s with
  v0 :: VArgs (v2s) :: s -> apply8s v0 v2s vs c s r t m

(* return : i *)
let return = fun (VS (_)) c (v :: s) (VK (c', r') :: []) t m ->
  run_c8 c' (v :: s) r' t m

(* return' : i *)
let return' = fun (VK (c', r')) c (v :: s) r t m ->
  run_c8 c' (v :: s) r' t m

(* grab : i -> i *)
let grab i = fun (VS (vs)) c s r t m ->
  begin match (c, s, r) with
      (CSeq (i', c'), VArgs (v1 :: v2s) :: s', VS (vs') :: r')
        when i' == apply -> (*Grab*)
        (* print_endline ("grab: " ^ Value.s_to_string s); *)
        i (VS (v1 :: vs)) (CSeq (i' >>> c')) (VArgs (v2s) :: s')
          (VS (vs') :: r') t m
    | _ ->
        let vfun = VFun (fun _ s' (VK (c', r') :: []) t' m' ->
          begin match s' with
            v1 :: s' -> (i >> return) (VS (v1 :: vs)) C0
                                      s' (VK (c', r') :: []) t' m'
                     (* i (VS (v1 :: vs)) (CSeq (return', C0))
                          s' (VK (c', r') :: []) t' m' *)
          | _ -> failwith "stack error"
          end) in
        run_c8 c (vfun :: s) r t m
  end

(* shift : i -> i *)
let shift i = fun (VS (vs)) c s r t m ->
  i (VS (VContS (c, s, r, t) :: vs)) C0 [] [] TNil m

(* control : i -> i *)
let control i = fun (VS (vs)) c s r t m ->
  i (VS (VContC (c, s, r, t) :: vs)) C0 [] [] TNil m

(* shift0 : i -> i *)
let shift0 i = fun (VS (vs)) c s r t m -> match m with
    MCons ((c0, s0, r0, t0), m0) ->
    i (VS (VContS (c, s, r, t) :: vs)) c0 s0 r0 t0 m0
  | _ -> failwith "shift0 is used without enclosing reset"

(* control0 : i -> i *)
let control0 i = fun (VS (vs)) c s r t m -> match m with
    MCons ((c0, s0, r0, t0), m0) ->
    i (VS (VContC (c, s, r, t) :: vs)) c0 s0 r0 t0 m0
  | _ -> failwith "control0 is used without enclosing reset"

(* reset : i -> i *)
let reset i = fun (VS (vs)) c s r t m ->
  i (VS (vs)) C0 [] [] TNil (MCons ((c, s, r, t), m))

(* f8 : e -> string list -> c *)
let rec f8 e xs = match e with
    Num (n) -> num n >>> C0
  | Var (x) -> access (Env.offset x xs) >>> C0
  | Op (e0, op, e1) -> (* f8 e1 xs >> f8 e0 xs >> operation (op) *)
    (f8 e1 xs) >> (f8 e0 xs) >> (operation (op) >>> C0)
  | Fun (x, e) -> (grab (f8 e (x :: xs)) >>> C0)
  | App (e0, e2s) ->
    (f8s e2s xs) >> (f8 e0 xs) >> (apply >>> C0)
  | Shift (x, e) -> (shift (f8 e (x :: xs)) >>> C0)
  | Control (x, e) -> (control (f8 e (x :: xs)) >>> C0)
  | Shift0 (x, e) -> (shift0 (f8 e (x :: xs)) >>> C0)
  | Control0 (x, e) -> (control0 (f8 e (x :: xs)) >>> C0)
  | Reset (e) -> (reset (f8 e xs) >>> C0)

(* f8s : e list -> string list -> c *)
and f8s e2s xs = match e2s with
    [] -> (pushmark >>> C0)
  | e :: e2s -> (f8s e2s xs) >> (f8 e xs) >> (push >>> C0)

(* f : e -> v *)
let f expr = run_c8 (f8 expr []) (VS ([])) C0 [] [] TNil MNil
