open Syntax
open Value

(* Refunctionalized interpreter : eval6 *)

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

(* f6 : e -> string list -> v list -> c -> s -> t -> m -> v *)
let rec f6 e xs vs c s t m = match e with
    Num (n) -> c (VNum (n)) s t m
  | Var (x) -> c (List.nth vs (Env.offset x xs)) s t m
  | Op (e0, op, e1) ->
    f6 e1 xs vs (fun v1 s1 t1 m1 ->
        begin match s1 with
            VEnv (vs) :: s1 ->
            f6 e0 xs vs (fun v0 s0 t0 m0 ->
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
                end) (v1 :: s1) t1 m1
          | _ -> failwith "stack error op2"
        end) (VEnv (vs) :: s) t m
  | Fun (x, e) ->
    c (VFun (fun v vs_out c' s' t' m' -> (* add vs_out *)
      f6t e (x :: xs) (v :: vs) c' (VArgs (vs_out) :: s') t' m')) s t m (* change f6 to f6t *)
  | App (e0, e1, e2s) ->
    f6s e2s xs vs (* expanding CApp2 (e0, e1, xs, c) *)
      (fun v2s s2s t2s m2s ->
        begin match s2s with VEnv (vs) :: s ->
          f6 e1 xs vs (* expanding CApp1 (e0, xs, c) *)
            (fun v1 s1 t1 m1 ->
              begin match s1 with VEnv (v2s) :: VEnv (vs) :: s ->
                f6 e0 xs vs (* expanding CApp0 (c) *)
                  (fun v0 s0 t0 m0 ->
                    begin match s0 with VEnv (v1 :: v2s) :: s ->
                      apply6 v0 v1 c (VArgs (v2s) :: s) t0 m0
                    end
                  ) (VEnv (v1 :: v2s) :: s) t1 m1
              end
            ) (VEnv (v2s) :: VEnv (vs) :: s) t2s m2s
        end
      ) (VEnv (vs) :: s) t m
  | Shift (x, e) -> f6 e (x :: xs) (VContS (c, s, t) :: vs) idc [] TNil m
  | Control (x, e) -> f6 e (x :: xs) (VContC (c, s, t) :: vs) idc [] TNil m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f6 e (x :: xs) (VContS (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        f6 e (x :: xs) (VContC (c, s, t) :: vs) c0 s0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f6 e xs vs idc [] TNil (MCons ((c, s, t), m))

(* f6s: e list -> string list -> v list -> s -> t -> m *)
and f6s es xs vs c s t m = match es with
    [] -> c [] s t m
  | first :: rest ->
    f6s rest xs vs (* expanding CAppS1 (first, xs, c) *)
      (fun v1 s1 t1 m1 ->
        begin match s1 with VEnv (vs) :: s ->
          f6 first xs vs (* expanding CAppS0 (cs) *)
            (fun v2 s2 t2 m2 ->
              begin match s2 with VEnv (v2s) :: s ->
                c (v2 :: v2s) s t2 m2
              end
            ) (VEnv (v1) :: s) t1 m1
        end
      ) (VEnv (vs) :: s) t m

and f6t e xs vs c s t m =
  let ret v (VEnv (vs_out) :: s) t m = match vs_out with (* expanding CRet (c) *)
      [] -> c v s t m
    | first :: rest -> apply6 v first c (VArgs (rest) :: s) t m in
  match s with (VArgs (vs_out) :: s) ->
    begin match e with
      Num (n) -> ret (VNum (n)) (VEnv (vs_out) :: s) t m
    | Var (x) -> ret (List.nth vs (Env.offset x xs)) (VEnv (vs_out) :: s) t m
    | Op (e0, op, e1) ->
      f6 e1 xs vs (fun v1 s1 t1 m1 ->
          begin match s1 with
              VEnv (vs) :: VEnv (vs_out) :: s1 ->
              f6 e0 xs vs (fun v0 s0 t0 m0 ->
                  begin match s0 with
                      v1 :: VEnv (vs_out) :: s0 ->
                      begin match (v0, v1) with
                          (VNum (n0), VNum (n1)) ->
                          begin match op with
                              Plus -> ret (VNum (n0 + n1)) (VEnv (vs_out) :: s0) t0 m0
                            | Minus -> ret (VNum (n0 - n1)) (VEnv (vs_out) :: s0) t0 m0
                            | Times -> ret (VNum (n0 * n1)) (VEnv (vs_out) :: s0) t0 m0
                            | Divide ->
                              if n1 = 0 then failwith "Division by zero"
                              else ret (VNum (n0 / n1)) (VEnv (vs_out) :: s0) t0 m0
                          end
                        | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                                        ^ " are not numbers")
                      end
                    | _ -> failwith "stack error op1"
                  end) (v1 :: VEnv (vs_out) :: s1) t1 m1
            | _ -> failwith "stack error op2"
          end) (VEnv (vs) :: VEnv (vs_out) :: s) t m
    | Fun (x, e) ->
      begin match vs_out with
          [] -> c (VFun (fun v vs_out c' s' t' m' ->
                  f6t e (x :: xs) (v :: vs) c' (VArgs (vs_out) :: s') t' m')) s t m (* adding vs_out, change f5 to f5t *)
        | first :: rest -> f6t e (x :: xs) (first :: vs) c (VArgs (rest) :: s) t m
      end
    | App (e0, e1, e2s) ->
      f6st e2s xs vs (* expanding CApp2 (e0, e1, xs, c) *)
        (fun v2s s2s t2s m2s ->
          begin match s2s with VEnv (vs) :: s ->
            f6 e1 xs vs (* expanding CApp1 (e0, xs, c) *)
              (fun v1 s1 t1 m1 ->
                begin match s1 with VEnv (v2s) :: VEnv (vs) :: s ->
                  f6 e0 xs vs (* expanding CApp0 (c) *)
                    (fun v0 s0 t0 m0 ->
                      begin match s0 with VEnv (v1 :: v2s) :: s ->
                        apply6 v0 v1 c (VArgs (v2s) :: s) t0 m0
                      end
                    ) (VEnv (v1 :: v2s) :: s) t1 m1
                end
              ) (VEnv (v2s) :: VEnv (vs) :: s) t2s m2s
          end
        ) (VArgs (vs_out) :: VEnv (vs) :: s) t m
    | Shift (x, e) -> f6 e (x :: xs) (VContS (c, s, t) :: vs) idc [] TNil m
    | Control (x, e) -> f6 e (x :: xs) (VContC (c, s, t) :: vs) idc [] TNil m
    | Shift0 (x, e) ->
      begin match m with
          MCons ((c0, s0, t0), m0) ->
          f6 e (x :: xs) (VContS (c, s, t) :: vs) c0 s0 t0 m0
        | _ -> failwith "shift0 is used without enclosing reset"
      end
    | Control0 (x, e) ->
      begin match m with
          MCons ((c0, s0, t0), m0) ->
          f6 e (x :: xs) (VContC (c, s, t) :: vs) c0 s0 t0 m0
        | _ -> failwith "control0 is used without enclosing reset"
      end
    | Reset (e) -> f6 e xs vs idc [] TNil (MCons ((c, s, t), m))
    end
and f6st e2s xs vs cs s t m = match s with (VArgs (vs_out) :: s) ->
  begin match e2s with
      [] -> cs vs_out s t m
    | first :: rest ->
      f6st rest xs vs (* expanding CAppS1 (first, xs, c) *)
        (fun v1 s1 t1 m1 ->
          begin match s1 with VEnv (vs) :: s ->
            f6 first xs vs (* expanding CAppS0 (cs) *)
              (fun v2 s2 t2 m2 ->
                begin match s2 with VEnv (v2s) :: s ->
                  cs (v2 :: v2s) s t2 m2
                end
              ) (VEnv (v1) :: s) t1 m1
          end
        ) (VArgs (vs_out) :: VEnv (vs) :: s) t m
    end

(* apply6 : v -> v -> v list -> c -> s -> t -> m -> v *)
and apply6 v0 v1 c s t m = match s with (VArgs (v2s) :: s) ->
  begin match v0 with
      VFun (f) -> f v1 v2s c s t m
    | VContS (c', s', t') -> c' v1 s' t' (MCons ((c, s, t), m))
    | VContC (c', s', t') ->
      c' v1 s' (apnd t' (cons (fun v t m -> c v s t m) t)) m
    | _ -> failwith (to_string v0
                      ^ " is not a function; it can not be applied.")
  end

(* f : e -> v *)
let f expr = f6 expr [] [] idc [] TNil MNil
