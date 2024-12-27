open Syntax
open Value

(* Interpreter using combinators factored as instructions *)
(* with return stack (r), where continution is defuntionalized (d): eval8rd *)
(* 'f8' here is inline-expanded *)

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

(* run_c8 : c -> s -> t -> m -> v *)
let rec run_c8 c s t m = match (c, s) with
    (C0, v :: []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> run_c8 c (v :: s) t m
        end
      | Trail (h) -> h v TNil m
    end
  | (COp0 (op, vs, c), v0 :: v1 :: s) ->
                   begin match (v0, v1) with
                     (VNum (n0), VNum (n1)) ->
                       begin match op with
                         Plus -> run_c8 c (VNum (n0 + n1) :: s)  t m
                       | Minus -> run_c8 c (VNum (n0 - n1) :: s)  t m
                       | Times -> run_c8 c (VNum (n0 * n1) :: s)  t m
                       | Divide ->
                         if n1 = 0 then failwith "Division by zero"
                         else run_c8 c (VNum (n0 / n1) :: s)  t m
                       end
                     | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                                      ^ " are not numbers")
                   end
  | (COp1 (e0, xs, op, vs, c), v1 :: s) ->
    f8 e0 xs vs (COp0 (op, vs, c)) (v1 :: s) t m
  | (CApp0 (vs, c), v0 :: VArg (v1) :: s) ->
    apply8 v0 v1 c s t m
  | (CApp1 (e0, xs, vs, c), v :: s) ->
    f8 e0 xs vs (CApp0 (vs, c)) (VArg (v) :: s) t m

(* apply8 : v -> v -> c -> s -> t -> m -> v *)
and apply8 v0 v1 c s t m = match v0 with
    VFun (f) -> f c (v1 :: s) t m
  | VContS (c', s', t') ->
    run_c8 c' (v1 :: s') t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    run_c8 c' (v1 :: s')
           (apnd t' (cons (fun v t m -> run_c8 c (v :: s) t m) t)) m
  | _ -> failwith (to_string v0
                    ^ " is not a function; it cannot be applied.")

(* f8 : e -> string list -> i *)
and f8 e xs vs c s t m = match e with
    Num (n) ->
    run_c8 c (VNum (n) :: s) t m
  | Var (x) ->
    run_c8 c (List.nth vs (Env.offset x xs) :: s) t m
  | Op (e0, op, e1) ->
    f8 e1 xs vs (COp1 (e0, xs, op, vs, c)) s t m
  | Fun (x, e) ->
    begin match (c, s) with
        (CApp0 (_, c'), VArg (v1) :: s') -> (* Grab *)
          (* print_endline ("grab: " ^ Value.s_to_string s); *)
          f8 e (x :: xs) (v1 :: vs) c' s' t m
      | _ ->
        let vfun = VFun (fun c' s' t' m' ->
          begin match s' with
            v :: s' -> f8 e (x :: xs) (v :: vs) c' s' t' m'
          | _ -> failwith "stack error"
          end) in
        run_c8 c (vfun :: s) t m
    end
  | App (e0, e1, _) ->
    f8 e1 xs vs (CApp1 (e0, xs, vs, c)) s t m
  | Shift (x, e) ->
    f8 e (x :: xs) (VContS (c, s, t) :: vs) idc [] TNil m
  | Control (x, e) ->
    f8 e (x :: xs) (VContC (c, s, t) :: vs) idc [] TNil m
  | Shift0 (x, e) ->
      begin match m with
          MCons ((c0, s0, t0), m0) ->
          f8 e (x :: xs) (VContS (c, s, t) :: vs) c0 s0 t0 m0
        | _ -> failwith "shift0 is used without enclosing reset"
      end
  | Control0 (x, e) ->
      begin match m with
          MCons ((c0, s0, t0), m0) ->
          f8 e (x :: xs) (VContC (c, s, t) :: vs) c0 s0 t0 m0
        | _ -> failwith "control0 is used without enclosing reset"
      end
  | Reset (e) ->
    f8 e xs vs idc [] TNil (MCons ((c, s, t), m))

(* f : e -> v *)
let f expr = f8 expr [] [] idc [] TNil MNil
