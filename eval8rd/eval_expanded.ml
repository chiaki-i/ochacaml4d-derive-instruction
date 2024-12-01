open Syntax
open Value

(* Interpreter using combinators factored as instructions *)
(* with return stack (r), where continution is defuntionalized (d): eval8rd *)
(* 'f8' here is inline-expanded *)

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
  | (CSeq (i1, c), (v :: s), (VEnv (vs) :: r)) ->
    i1 vs c (v :: s) r t m
    (*
  | (CSeq2 (i1, c), (v :: s), (VEnv (vs) :: r)) ->
    i1 vs c (VArg (v) :: s) r t m
    *)

(* initial continuation : s -> t -> m -> v *)
let idc = C0

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
  (* print_endline (Value.s_to_string s); *)
  i0 vs (CSeq (i1, c)) s (VEnv (vs) :: r) t m

(*
(* (>>>) : i -> i -> i *)
let (>>>) i0 i1 = fun vs c s r t m ->
  i0 vs (CSeq2 (i1, c)) s (VEnv (vs) :: r) t m

(* (>>>>) : i -> i -> i *)
let (>>>>) i0 i1 = fun vs c (VArg (v) :: s) r t m ->
  i0 vs (CSeq (i1, c)) (VArg2 (v, c) :: s) (VEnv (vs) :: r) t m
*)

(* (f8 e1 xs >>> f8 e0 xs) >> apply *)
(*  f8 e1 xs >>> (f8 e0 xs >> apply) *)

(* varg : i *)
let varg = fun vs c (v :: s) r t m -> run_c8 c (VArg (v) :: s) r t m

(* num : int -> i *)
let num n = fun vs c s r t m -> run_c8 c (VNum (n) :: s) r t m

(* access : int -> i *)
let access n = fun vs c s r t m -> run_c8 c (List.nth vs n :: s) r t m

(* operation : op -> i *)
let operation op = fun vs c s r t m -> match (s, r) with
    (v0 :: v1 :: s, r) ->
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

(* apply8 : v -> v -> c -> s -> r -> t -> m -> v *)
let apply8 v0 v1 c s r t m = match v0 with
    VFun (f) -> f c (v1 :: s) r t m
  | VContS (c', s', r', t') ->
    run_c8 c' (v1 :: s') r' t' (MCons ((c, s, r, t), m))
  | VContC (c', s', r', t') ->
    run_c8 c' (v1 :: s') r'
           (apnd t' (cons (fun v t m -> run_c8 c (v :: s) r t m) t)) m
  | _ -> failwith (to_string v0
                    ^ " is not a function; it cannot be applied.")

(* apply : i *)
let apply = fun vs c s r t m -> match (s, r) with
  (v0 :: VArg (v1) :: s, r) -> apply8 v0 v1 c s r t m

(* grab : i -> i *)
let grab i = fun vs c s r t m ->
  begin match (c, s, r) with
      (CSeq (i', c'), VArg (v1) :: s', (VEnv (_) :: r)) when i' == apply -> (* Grab *)
        (* print_endline ("grab: " ^ Value.s_to_string s); *)
        i (v1 :: vs) c' s' r t m
    | _ ->
        let vfun = VFun (fun c' s' r' t' m' ->
          begin match (s', r') with
            (v :: s', r') -> i (v :: vs) c' s' r' t' m'
          | _ -> failwith "stack error"
          end) in
        run_c8 c (vfun :: s) r t m
  end

(*
  run_c8 (CSeq (apply, c')) (vfun :: v1 :: s) (VEnv (vs) :: r) t m
= apply vs c' (vfun :: v1 :: s) r t m
= apply8 vfun v1 c' s r t m
= f c' (v1 :: s) r t m
= i (v1 :: vs) c' s r t m
*)

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

(* f8 : e -> string list -> i *)
let rec f8 e xs = match e with
    Num (n) -> (* num n *)
    fun vs c s r t m ->
      run_c8 c (VNum (n) :: s) r t m
  | Var (x) -> (* access (Env.offset x xs) *)
    fun vs c s r t m ->
      run_c8 c (List.nth vs (Env.offset x xs) :: s) r t m
  | Op (e0, op, e1) ->
    (* f8 e1 xs >> f8 e0 xs >> operation (op) *)
    (* (* >> *) fun vs c s r t m -> i0 vs (CSeq (i1, c)) s (VEnv (vs) :: r) t m *)
    (* (* 途中 *) fun vs c s r t m -> f8 e1 xs vs (CSeq ((f8 e0 xs >> operation (op)), c)) s (VEnv (vs) :: r) t m *)
    fun vs c s r t m -> f8 e1 xs vs (CSeq
      ((fun vs c s r t m ->
        f8 e0 xs vs (CSeq
          ((fun vs c s r t m ->
            begin match (s, r) with
                (v0 :: v1 :: s, r) ->
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
            end), c))
          s (VEnv (vs) :: r) t m), c))
      s (VEnv (vs) :: r) t m
  | Fun (x, e) -> (* grab (f8 e (x :: xs)) *)
    fun vs c s r t m ->
    begin match (c, s, r) with
        (CSeq (i', c'), VArg (v1) :: s', (VEnv (_) :: r)) when i' == apply -> (* Grab *)
          (* print_endline ("grab: " ^ Value.s_to_string s); *)
          f8 e (x :: xs) (v1 :: vs) c' s' r t m
      | _ ->
        let vfun = VFun (fun c' s' r' t' m' ->
          begin match (s', r') with
            (v :: s', r') -> f8 e (x :: xs) (v :: vs) c' s' r' t' m'
          | _ -> failwith "stack error"
          end) in
        run_c8 c (vfun :: s) r t m
    end
  | App (e0, e1, _) ->
    (* f8 e1 xs >> varg >> f8 e0 xs >> apply *)
    (* (* >> *) fun vs c s r t m -> i0 vs (CSeq (i1, c)) s (VEnv (vs) :: r) t m *)
    fun vs c s r t m -> f8 e1 xs vs (CSeq
      ((fun vs c s r t m ->
        (fun vs c (v :: s) r t m -> run_c8 c (VArg (v) :: s) r t m) (* varg *)
        vs (CSeq
          ((fun vs c s r t m ->
            f8 e0 xs vs (CSeq (
              (fun vs c s r t m -> match (s, r) with
                (v0 :: VArg (v1) :: s, r) -> apply8 v0 v1 c s r t m), c))
            s (VEnv (vs) :: r) t m), c))
        s (VEnv (vs) :: r) t m), c))
      s (VEnv (vs) :: r) t m
  | Shift (x, e) -> (* shift (f8 e (x :: xs)) *)
    fun vs c s r t m -> f8 e (x :: xs) (VContS (c, s, r, t) :: vs) idc [] [] TNil m
  | Control (x, e) -> (* control (f8 e (x :: xs)) *)
    fun vs c s r t m -> f8 e (x :: xs) (VContC (c, s, r, t) :: vs) idc [] [] TNil m
  | Shift0 (x, e) -> (* shift0 (f8 e (x :: xs)) *)
    fun vs c s r t m ->
      begin match m with
          MCons ((c0, s0, r0, t0), m0) ->
          f8 e (x :: xs) (VContS (c, s, r, t) :: vs) c0 s0 r0 t0 m0
        | _ -> failwith "shift0 is used without enclosing reset"
      end
  | Control0 (x, e) -> (* control0 (f8 e (x :: xs)) *)
    fun vs c s r t m ->
      begin match m with
          MCons ((c0, s0, r0, t0), m0) ->
          f8 e (x :: xs) (VContC (c, s, r, t) :: vs) c0 s0 r0 t0 m0
        | _ -> failwith "control0 is used without enclosing reset"
      end
  | Reset (e) -> (* reset (f8 e xs) *)
    fun vs c s r t m ->
    f8 e xs vs idc [] [] TNil (MCons ((c, s, r, t), m))

(* f : e -> v *)
let f expr = f8 expr [] [] idc [] [] TNil MNil
