open Syntax
open Value

(* Interpreter with combining arguments : eval7 *)

(* initial continuation : s -> t -> m -> v *)
let idc s t m = match s with
    v :: [] ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t), m) -> c (v :: s) t m
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

(* f7 : e -> string list -> v list -> c -> s -> t -> m -> v *)
let rec f7 e xs vs c s t m =
  begin match e with
      Num (n) -> c (VNum (n) :: s) t m
    | Var (x) -> c ((List.nth vs (Env.offset x xs)) :: s) t m
    | Op (e0, op, e1) ->
      f7 e1 xs vs (fun s1 t1 m1 ->
          begin match s1 with
              v1 :: VEnv (vs) :: s1 -> (* VNum を Stack から取り出す *)
              f7 e0 xs vs (fun s0 t0 m0 ->
                  begin match s0 with
                      v0 :: v1 :: s0 -> (* VNum を Stack から取り出す *)
                      begin match (v0, v1) with
                          (VNum (n0), VNum (n1)) ->
                          begin match op with
                              Plus -> c (VNum (n0 + n1) :: s0) t0 m0
                            | Minus -> c (VNum (n0 - n1) :: s0) t0 m0
                            | Times -> c (VNum (n0 * n1) :: s0) t0 m0
                            | Divide ->
                              if n1 = 0 then failwith "Division by zero"
                              else c (VNum (n0 / n1) :: s0) t0 m0
                          end
                        | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                                          ^ " are not numbers")
                      end
                    | _ -> failwith "stack error op1"
                  end) (v1 :: s1) t1 m1
            | _ -> failwith "stack error"
          end) (VEnv (vs) :: s) t m
    | Fun (x, e) ->
      let vfun = VFun (fun c' s' t' m' ->
          begin match s' with
              v :: s' -> f7 e (x :: xs) (v :: vs) c' s' t' m'
            | _ -> failwith "stack error"
          end) in
      c (vfun :: s) t m
    | App (e0, e1, e2s) ->
      f7s e2s xs vs
        (fun s2s t2s m2s ->
          begin match s2s with VEnv (v2s) :: VEnv (vs) :: s -> (* v2s : v list *)
            f7 e1 xs vs
              (fun s1 t1 m1 ->
                begin match s1 with v1 :: VEnv (v2s) :: VEnv (vs) :: s -> (* v1 : v *)
                  f7 e0 xs vs
                    (fun s0 t0 m0 ->
                      begin match s0 with v0 :: VEnv (v1 :: v2s) :: s -> (* v0 : v *)
                        apply7 v0 v1 v2s c s t0 m0
                      end
                    ) (VEnv (v1 :: v2s) :: s) t1 m1
                end
              ) (VEnv (v2s) :: VEnv (vs) :: s) t2s m2s
          end
        ) (VEnv (vs) :: s) t m
    | Shift (x, e) ->
      f7 e (x :: xs) (VContS (c, s, t) :: vs) idc [] TNil m
    | Control (x, e) ->
      f7 e (x :: xs) (VContC (c, s, t) :: vs) idc [] TNil m
    | Shift0 (x, e) ->
      begin match m with
          MCons ((c0, s0, t0), m0) ->
          f7 e (x :: xs) (VContS (c, s, t) :: vs) c0 s0 t0 m0
        | _ -> failwith "shift0 is used without enclosing reset"
      end
    | Control0 (x, e) ->
      begin match m with
          MCons ((c0, s0, t0), m0) ->
          f7 e (x :: xs) (VContC (c, s, t) :: vs) c0 s0 t0 m0
        | _ -> failwith "control0 is used without enclosing reset"
      end
    | Reset (e) -> f7 e xs vs idc [] TNil (MCons ((c, s, t), m))
  end
(* f7s: e list -> string list -> v list -> s -> t -> m *)
and f7s es xs vs c s t m =
    begin match es with
      [] -> c (VEnv ([]) :: s) t m (* [] = Pushmark の ε に相当 *)
    | first :: rest ->
      f7s rest xs vs
        (fun s1 t1 m1 ->
          begin match s1 with VEnv (v1) :: VEnv (vs) :: s ->
            f7 first xs vs
              (fun s2 t2 m2 ->
                begin match s2 with v2 :: VEnv (v2s) :: s ->
                  c (VEnv (v2 :: v2s) :: s) t2 m2 (* v2 :: VEnv (v2s) :: s にしなくて良いか検証 *)
                end
              ) (VEnv (v1) :: s) t1 m1
          end
        ) (VEnv (vs) :: s) t m
    end
(* apply7 : v -> v -> v list -> c -> s -> t -> m -> v *)
and apply7 v0 v1 v2s c s t m =
  app7 v0 v1 (fun (v2 :: VEnv (v2s) :: s2) t2 m2 ->
    begin match v2s with
        [] -> c (v2 :: s2) t2 m2
      | first :: rest -> apply7 v2 first rest c s2 t2 m2
    end
    ) (VEnv (v2s) :: s) t m
(* app7 : v -> v -> c -> s -> t -> m -> v *)
and app7 v0 v1 c s t m = match v0 with
      VFun (f) -> f c (v1 :: s) t m
    | VContS (c', s', t') -> c' (v1 :: s') t' (MCons ((c, s, t), m))
    | VContC (c', s', t') ->
      c' (v1 :: s')
        (apnd t' (cons (fun v t m -> c (v :: s) t m) t)) m
    | _ -> failwith (to_string v0
                      ^ " is not a function; it can not be applied.")

(* f : e -> v *)
let f expr = f7 expr [] [] idc [] TNil MNil
