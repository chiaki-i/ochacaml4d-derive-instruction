open Syntax
open Value

(* Delinearized interpreter : eval5 *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c5 : c -> v -> s -> t -> m -> v *)
let rec run_c5 c v s t m = match s with
  VArgs (vs_out) :: s ->
    begin match (c, s) with
        (C0, []) ->
        begin match t with
            TNil ->
            begin match m with
                MNil -> v
              | MCons ((c, s, t), m) -> run_c5 c v (VArgs (vs_out) :: s) t m
            end
          | Trail (h) -> h v TNil m
        end
      | (CApp0 (c), v1 :: VEnv (v2s) :: s) ->
        apply5 v v1 v2s c (VArgs (vs_out) :: s) t m
      | (CApp1 (e0, xs, c), VEnv (v2s) :: VEnv (vs) :: s) ->
        f5 e0 xs vs (CApp0 (c)) (VArgs (vs_out) :: v :: VEnv (v2s) :: s) t m
      | (CAppS0 (cs), VEnv (v2s) :: s) ->
        runs_c5 cs (v :: v2s) (VArgs (vs_out) :: s) t m
      | (CRet (c), s) ->
        begin match vs_out with
            [] -> run_c5 c v (VArgs (vs_out) :: s) t m
          | first :: rest -> apply5 v first rest c (VArgs (vs_out) :: s) t m
        end
      | (COp0 (e0, xs, op, c), VEnv (vs) :: s) ->
        f5 e0 xs vs (COp1 (op, c)) (VArgs (vs_out) :: v :: s) t m
      | (COp1 (op, c), v0 :: s) ->
        begin match (v, v0) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c5 c (VNum (n0 + n1)) (VArgs (vs_out) :: s) t m
              | Minus -> run_c5 c (VNum (n0 - n1)) (VArgs (vs_out) :: s) t m
              | Times -> run_c5 c (VNum (n0 * n1)) (VArgs (vs_out) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c5 c (VNum (n0 / n1)) (VArgs (vs_out) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
        end
      | (COp2 (e0, xs, op, c), VEnv (vs) :: s) -> (* tail version *)
        f5 e0 xs vs (COp3 (op, c)) (VArgs (vs_out) :: v :: s) t m
      | (COp3 (op, c), v0 :: s) -> (* tail version *)
        begin match (v, v0) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c5 (CRet (c)) (VNum (n0 + n1)) (VArgs (vs_out) :: s) t m
              | Minus -> run_c5 (CRet (c)) (VNum (n0 - n1)) (VArgs (vs_out) :: s) t m
              | Times -> run_c5 (CRet (c)) (VNum (n0 * n1)) (VArgs (vs_out) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c5 (CRet (c)) (VNum (n0 / n1)) (VArgs (vs_out) :: s) t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v ^ " are not numbers")
        end
      | _ -> failwith "stack or cont error"
    end
  | _ -> failwith "runs_c5: vs_out is missing"
(* runs_c5: c -> v list -> s -> t -> m -> v *)
and runs_c5 c v s t m = match s with
  VArgs (vs_out) :: s ->
    begin match (c, s) with
        (CApp2 (e0, e1, xs, c), VEnv (vs) :: s) ->
        f5 e1 xs vs (CApp1 (e0, xs, c)) (VArgs (vs_out) :: VEnv (v) :: VEnv (vs) :: s) t m
      | (CAppS1 (first, xs, cs), VEnv (vs) :: s) ->
        f5 first xs vs (CAppS0 (cs)) (VArgs (vs_out) :: VEnv (v) :: s) t m
      | _ -> failwith "runs_c5: unexpected continuation or stack"
    end
  | _ -> failwith "runs_c5: vs_out is missing"
(* apply5 : v -> v -> v list -> c -> s -> t -> m -> v *)
and apply5 v0 v1 v2s c s t m = match s with
  VArgs (vs_out) :: s ->
    begin match v0 with
        VFun (f) -> f v1 v2s c s t m
      | VContS (c', s', t') -> run_c5 c' v1 (VArgs (vs_out) :: s') t' (MCons ((c, s, t), m))
      | VContC (c', s', t') ->
        run_c5 c' v1 (VArgs (vs_out) :: s') (apnd t' (cons (fun v t m -> run_c5 c v (VArgs (vs_out) :: s) t m) t)) m
      | _ -> failwith (to_string v0
                        ^ " is not a function; it can not be applied.")
    end
  | _ -> failwith "apply5: vs_out is missing"

(* f5 : e -> string list -> v list -> c -> s -> t -> m -> v *)
and f5 e xs vs c s t m = match s with
  VArgs (vs_out) :: s ->
    begin match e with
        Num (n) -> run_c5 c (VNum (n)) (VArgs (vs_out) :: s) t m
      | Var (x) -> run_c5 c (List.nth vs (Env.offset x xs)) (VArgs (vs_out) :: s) t m
      | Op (e0, op, e1) ->
        f5 e1 xs vs (COp0 (e0, xs, op, c)) (VArgs (vs_out) :: VEnv (vs) :: s) t m
      | Fun (x, e) ->
        run_c5 c (VFun (fun v v2s c' s' t' m' ->
          f5t e (x :: xs) (v :: vs) c' (VArgs (v2s) :: s') t' m')) (VArgs (vs_out) :: s) t m
      | App (e0, e1, e2s) ->
        f5s e2s xs vs (CApp2 (e0, e1, xs, c)) (VArgs (vs_out) :: VEnv (vs) :: s) t m
      | Shift (x, e) -> f5 e (x :: xs) (VContS (c, s, t) :: vs) C0 [VArgs (vs_out)] TNil m
      | Control (x, e) -> f5 e (x :: xs) (VContC (c, s, t) :: vs) C0 [VArgs (vs_out)] TNil m
      | Shift0 (x, e) ->
        begin match m with
            MCons ((c0, s0, t0), m0) ->
            f5 e (x :: xs) (VContS (c, s, t) :: vs) c0 (VArgs (vs_out) :: s0) t0 m0
          | _ -> failwith "shift0 is used without enclosing reset"
        end
      | Control0 (x, e) ->
        begin match m with
            MCons ((c0, s0, t0), m0) ->
            f5 e (x :: xs) (VContC (c, s, t) :: vs) c0 (VArgs (vs_out) :: s0) t0 m0
          | _ -> failwith "control0 is used without enclosing reset"
        end
      | Reset (e) -> f5 e xs vs C0 [VArgs (vs_out)] TNil (MCons ((c, s, t), m))
    end
  | _ -> failwith "f5: vs_out is missing"
(* f5s: e list -> string list -> v list -> s -> t -> m *)
and f5s es xs vs c s t m = match s with
  VArgs (vs_out) :: s ->
    begin match es with
        [] -> runs_c5 c [] (VArgs (vs_out) :: s) t m
      | first :: rest ->
        f5s rest xs vs (CAppS1 (first, xs, c)) (VArgs (vs_out) :: VEnv (vs) :: s) t m
    end
  | _ -> failwith "f5s: vs_out is missing"

and f5t e xs vs c s t m = match s with
  VArgs (vs_out) :: s ->
    begin match e with
        Num (n) -> run_c5 (CRet (c)) (VNum (n)) (VArgs (vs_out) :: s) t m
      | Var (x) -> run_c5 (CRet (c)) (List.nth vs (Env.offset x xs)) (VArgs (vs_out) :: s) t m
      | Op (e0, op, e1) ->
        f5 e1 xs vs (COp2 (e0, xs, op, c)) (VArgs (vs_out) :: VEnv (vs) :: s) t m
      | Fun (x, e) ->
        begin match vs_out with
            [] -> run_c5 c (VFun (fun v v2s c' s' t' m' ->
                    f5t e (x :: xs) (v :: vs) c' (VArgs (v2s) :: s') t' m')) (VArgs (vs_out) :: s) t m
          | first :: rest -> f5t e (x :: xs) (first :: vs) c (VArgs (rest) :: s) t m
        end
      | App (e0, e1, e2s) ->
        f5st e2s xs vs (CApp2 (e0, e1, xs, c)) (VArgs (vs_out) :: VEnv (vs) :: s) t m
      | Shift (x, e) -> f5 e (x :: xs) (VContS (c, s, t) :: vs) C0 [VArgs (vs_out)] TNil m
      | Control (x, e) -> f5 e (x :: xs) (VContC (c, s, t) :: vs) C0 [VArgs (vs_out)] TNil m
      | Shift0 (x, e) ->
        begin match m with
            MCons ((c0, s0, t0), m0) ->
            f5 e (x :: xs) (VContS (c, s, t) :: vs) c0 (VArgs (vs_out) :: s0) t0 m0
          | _ -> failwith "shift0 is used without enclosing reset"
        end
      | Control0 (x, e) ->
        begin match m with
            MCons ((c0, s0, t0), m0) ->
            f5 e (x :: xs) (VContC (c, s, t) :: vs) c0 (VArgs (vs_out) :: s0) t0 m0
          | _ -> failwith "control0 is used without enclosing reset"
        end
      | Reset (e) -> f5 e xs vs C0 [VArgs (vs_out)] TNil (MCons ((c, s, t), m))
    end
  | _ -> failwith "f5t: vs_out is missing"
and f5st e2s xs vs cs s t m = match s with
  VArgs (vs_out) :: s ->
    begin match e2s with
        [] -> runs_c5 cs vs_out (VArgs (vs_out) :: s) t m
      | first :: rest ->
        f5st rest xs vs (CAppS1 (first, xs, cs)) (VArgs (vs_out) :: VEnv (vs) :: s) t m
    end
  | _ -> failwith "f5st: vs_out is missing"

(* f : e -> v *)
let f expr = f5 expr [] [] C0 [VArgs ([])] TNil MNil
