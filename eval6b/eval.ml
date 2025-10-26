open Syntax
open Value

(* interpreter with accumulator : eval6b *)

(* initial continuation : v -> s -> t -> m -> v *)
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
  | _ -> failwith "stack error idc"

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* f : e -> string list -> v list -> c -> v -> s -> t -> m -> v *)
let rec f e xs vs c a s t m = match e with
    Num (n) -> c (VNum (n)) s t m
  | Var (x) -> c (List.nth vs (Env.off_set x xs)) s t m
  | Op (e0, op, e1) ->
    f e1 xs vs (fun v1 s1 t1 m1 ->
      f e0 xs vs (fun v0 s0 t0 m0 ->
        begin match s0 with
            v1 :: s0 ->
            begin match (v0, v1) with
                (VNum (n0), VNum (n1)) ->
                begin match op with
                    Plus -> c (VNum (n0 + n1)) s0 t0 m0
                  | Minus -> c (VNum (n0 - n1)) s0 t0 m0
                  | Times -> c (VNum (n0 * n1)) s0 t0 m0
                  | Divide ->
                    if n1 = 0 then failwith "Division by zero"
                    else c (VNum (n0 / n1)) s0 t0 m0
                end
              | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                                ^ " are not numbers")
            end
          | _ -> failwith "stack error op1"
        end) v1 (v1 :: s1) t1 m1
      ) a s t m
  | Fun (x, e) ->
    c (VFun (fun v vs_out c' s' t' m' -> (* add vs_out *)
      f_t e (x :: xs) (v :: vs) c' v (VArgs (vs_out) :: s') t' m')) s t m (* change f to f_t *)
  | App (e0, e1, e2s) ->
    f_s e2s xs vs (* expanding CApp2 (e0, e1, xs, c) *)
      (fun v2 s2 t2 m2 ->
          f e1 xs vs (* expanding CApp1 (e0, xs, c) *)
            (fun v1 s1 t1 m1 ->
                f e0 xs vs (* expanding CApp0 (c) *)
                  (fun v0 s0 t0 m0 ->
                    begin match s0 with v1 :: VEnv (v2s) :: s ->
                      app v0 v1 c (VArgs (v2s) :: s) t0 m0
                    end
                  ) v1 (v1 :: s1) t1 m1
            ) (v2) (v2 :: s2) t2 m2
      ) a s t m
  | Shift (x, e) -> f e (x :: xs) (VContS (c, s, t) :: vs) idc a [] TNil m
  | Control (x, e) -> f e (x :: xs) (VContC (c, s, t) :: vs) idc a [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f e (x :: xs) (VContS (c, s, t) :: vs) c0 a s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f e (x :: xs) (VContC (c, s, t) :: vs) c0 a s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f e xs vs idc a [] TNil (MCons ((c, s, t), m))

(* f_s: e list -> string list -> v list -> v -> s -> t -> m *)
and f_s es xs vs c a s t m = match es with
    [] -> c (VEnv ([])) s t m
  | first :: rest ->
    f_s rest xs vs (* expanding CAppS1 (first, xs, c) *)
      (fun (VEnv (v2s)) s2 t2 m2 ->
          f first xs vs (* expanding CAppS0 (cs) *)
            (fun v1 s1 t1 m1 ->
              begin match s1 with VEnv (v2s) :: s ->
                c (VEnv (v1 :: v2s)) s t1 m1
              end
            ) (VEnv (v2s)) (VEnv (v2s) :: s2) t2 m2
      ) a s t m

and ret c v (VEnv (vs_out) :: s) t m = match vs_out with (* expanding CRet (c) *)
    [] -> c v s t m
  | first :: rest -> app v first c (VArgs (rest) :: s) t m

and f_t e xs vs c a s t m = match s with (VArgs (vs_out) :: s) ->
  begin match e with
      Num (n) -> ret c (VNum (n)) (VEnv (vs_out) :: s) t m
    | Var (x) -> ret c (List.nth vs (Env.off_set x xs)) (VEnv (vs_out) :: s) t m
    | Op (e0, op, e1) ->
      f e1 xs vs (fun v1 s1 t1 m1 ->
        f e0 xs vs (fun v0 s0 t0 m0 ->
          begin match s0 with
              v1 :: s0 ->
              begin match (v0, v1) with
                  (VNum (n0), VNum (n1)) ->
                  begin match op with
                      Plus -> ret c (VNum (n0 + n1)) (VEnv (vs_out) :: s0) t0 m0
                    | Minus -> ret c (VNum (n0 - n1)) (VEnv (vs_out) :: s0) t0 m0
                    | Times -> ret c (VNum (n0 * n1)) (VEnv (vs_out) :: s0) t0 m0
                    | Divide ->
                      if n1 = 0 then failwith "Division by zero"
                      else ret c (VNum (n0 / n1)) (VEnv (vs_out) :: s0) t0 m0
                  end
                | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                                ^ " are not numbers")
              end
              | _ -> failwith "stack error op1"
            end) v1 (v1 :: s1) t1 m1
          ) a s t m
    | Fun (x, e) ->
      begin match vs_out with
          [] -> c (VFun (fun v vs_out c' s' t' m' ->
                  f_t e (x :: xs) (v :: vs) c' v (VArgs (vs_out) :: s') t' m')) s t m (* adding vs_out, change f to f_t *)
        | first :: rest -> f_t e (x :: xs) (first :: vs) c a (VArgs (rest) :: s) t m
      end
    | App (e0, e1, e2s) ->
      f_st e2s xs vs (* expanding CApp2 (e0, e1, xs, c) *)
        (fun v2 s2 t2 m2 ->
            f e1 xs vs (* expanding CApp1 (e0, xs, c) *)
              (fun v1 s1 t1 m1 ->
                  f e0 xs vs (* expanding CApp0 (c) *)
                    (fun v0 s0 t0 m0 ->
                      begin match s0 with v1 :: VEnv (v2s) :: s ->
                        app v0 v1 c (VArgs (v2s) :: s) t0 m0
                      end
                    ) v1 (v1 :: s1) t1 m1
              ) v2 (v2 :: s2) t2 m2
        ) a (VArgs (vs_out) :: s) t m
    | Shift (x, e) -> f e (x :: xs) (VContS (c, s, t) :: vs) idc a [] TNil m
    | Control (x, e) -> f e (x :: xs) (VContC (c, s, t) :: vs) idc a [] TNil m
    | Shift0 (x, e) ->
      begin match m with
          MCons ((c0, s0, t0), m0) ->
          f e (x :: xs) (VContS (c, s, t) :: vs) c0 a s0 t0 m0
        | _ -> failwith "shift0 is used without enclosing reset"
      end
    | Control0 (x, e) ->
      begin match m with
          MCons ((c0, s0, t0), m0) ->
          f e (x :: xs) (VContC (c, s, t) :: vs) c0 a s0 t0 m0
        | _ -> failwith "control0 is used without enclosing reset"
      end
    | Reset (e) -> f e xs vs idc a [] TNil (MCons ((c, s, t), m))
  end
and f_st e2s xs vs c a (VArgs (vs_out) :: s) t m = match e2s with
    [] -> c (VEnv (vs_out)) s t m
  | first :: rest ->
    f_st rest xs vs (* expanding CAppS1 (first, xs, c) *)
      (fun (VEnv v2s) s2 t2 m2 ->
          f first xs vs (* expanding CAppS0 (cs) *)
            (fun v1 s1 t1 m1 ->
              begin match s1 with VEnv (v2s) :: s ->
                c (VEnv (v1 :: v2s)) s t1 m1
              end
            ) (VEnv (v2s)) (VEnv (v2s) :: s2) t2 m2
      ) a (VArgs (vs_out) :: s) t m

(* app : v -> v -> v list -> c -> s -> t -> m -> v *)
  and app v0 v1 c (VArgs (v2s) :: s) t m = match v0 with
    VFun (f) -> f v1 v2s c s t m
  | VContS (c', s', t') -> c' v1 s' t' (MCons ((c, s, t), m))
  | VContC (c', s', t') ->
    c' v1 s' (apnd t' (cons (fun v t m -> c v s t m) t)) m
  | _ -> failwith (to_string v0
                    ^ " is not a function; it can not be applied.")


(* f_init : e -> v *)
let f_init expr = f expr [] [] idc (VNum 7) [] TNil MNil
