open Syntax
open Value

(* Refunctionalized interpreter : eval6 *)

(* initial continuation : v -> s -> t -> m -> v *)
let idc v s t m = match s with
  VArgs (vs_out) :: s ->
    begin match s with
        [] ->
        begin match t with
            TNil ->
            begin match m with
                MNil -> v
              | MCons ((c, s, t), m) -> c v (VArgs (vs_out) :: s) t m
            end
          | Trail (h) -> h v TNil m
        end
      | _ -> failwith "stack error idc"
    end
  | _ -> failwith "idc: vs_out is missing"

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* f6 : e -> string list -> v list -> c -> s -> t -> m -> v *)
let rec f6 e xs vs c s t m = match s with
  VArgs (vs_out) :: s ->
    begin match e with
        Num (n) -> c (VNum (n)) (VArgs (vs_out) :: s) t m
      | Var (x) -> c (List.nth vs (Env.offset x xs)) (VArgs (vs_out) :: s) t m
      | Op (e0, op, e1) ->
        f6 e1 xs vs (fun v1 (VArgs (vs_out') :: s1) t1 m1 ->
          f6 e0 xs vs (fun v0 (VArgs (vs_out) :: s0) t0 m0 ->
            begin match s0 with v1 :: s0 ->
                begin match (v0, v1) with
                    (VNum (n0), VNum (n1)) ->
                    begin match op with
                        Plus -> c (VNum (n0 + n1)) (VArgs (vs_out) :: s0) t0 m0
                      | Minus -> c (VNum (n0 - n1)) (VArgs (vs_out) :: s0) t0 m0
                      | Times -> c (VNum (n0 * n1)) (VArgs (vs_out) :: s0) t0 m0
                      | Divide ->
                        if n1 = 0 then failwith "Division by zero"
                        else c (VNum (n0 / n1)) (VArgs (vs_out) :: s0) t0 m0
                    end
                  | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                                  ^ " are not numbers")
                end
              | _ -> failwith "stack error op1"
            end) (VArgs (vs_out') :: v1 :: s1) t1 m1
            ) (VArgs (vs_out) :: s) t m
      | Fun (x, e) ->
        c (VFun (fun v v2s c' s' t' m' -> (* todo: v2s を s' に積むと良い *)
          f6t e (x :: xs) (v :: vs) c' (VArgs (v2s) :: s') t' m'))
            (VArgs (vs_out) :: s) t m
      | App (e0, e1, e2s) ->
        f6s e2s xs vs (* expanding CApp2 (e0, e1, xs, c) *)
          (fun (VEnv (v2s)) (VArgs (vs_out2) :: s2s) t2s m2s -> (* v2s = VEnv (_) の形 *)
              f6 e1 xs vs (* expanding CApp1 (e0, xs, c) *)
                (fun v1 (VArgs (vs_out1) :: s1) t1 m1 ->
                  begin match s1 with VEnv (v2s) :: s ->
                    f6 e0 xs vs (* expanding CApp0 (c) *)
                      (fun v0 (VArgs (vs_out0) :: s0) t0 m0 ->
                        begin match s0 with v1 :: VEnv (v2s) :: s ->
                          apply6 v0 v1 v2s c (VArgs (vs_out0) :: s) t0 m0
                        end
                      ) (VArgs (vs_out1) :: v1 :: VEnv (v2s) :: s) t1 m1
                  end
                ) (VArgs (vs_out2) :: VEnv (v2s) :: s2s) t2s m2s
          ) (VArgs (vs_out) :: s) t m
      | Shift (x, e) -> f6 e (x :: xs) (VContS (c, s, t) :: vs) idc [VArgs (vs_out)] TNil m
      | Control (x, e) -> f6 e (x :: xs) (VContC (c, s, t) :: vs) idc [VArgs (vs_out)] TNil m
      | Shift0 (x, e) ->
        begin match m with
            MCons ((c0, s0, t0), m0) ->
            f6 e (x :: xs) (VContS (c, s, t) :: vs) c0 (VArgs (vs_out) :: s0) t0 m0
          | _ -> failwith "shift0 is used without enclosing reset"
        end
      | Control0 (x, e) ->
        begin match m with
            MCons ((c0, s0, t0), m0) ->
            f6 e (x :: xs) (VContC (c, s, t) :: vs) c0 (VArgs (vs_out) :: s0) t0 m0
          | _ -> failwith "control0 is used without enclosing reset"
        end
      | Reset (e) -> f6 e xs vs idc [VArgs (vs_out)] TNil (MCons ((c, s, t), m))
    end
  | _ -> failwith "f6: vs_out is missing"

(* f6s: e list -> string list -> v list -> s -> t -> m *)
and f6s es xs vs c s t m = match s with
  VArgs (vs_out) :: s ->
    begin match es with
        [] -> c (VEnv ([])) (VArgs (vs_out) :: s) t m (* todo: introduce VMark *)
      | first :: rest ->
        f6s rest xs vs (* expanding CAppS1 (first, xs, c) *)
          (fun (VEnv (v2s)) (VArgs (vs_out2) :: s2) t2 m2 ->
              f6 first xs vs (* expanding CAppS0 (cs) *)
                (fun v1 (VArgs (vs_out1) :: s1) t1 m1 ->
                  begin match s1 with VEnv (v2s) :: s ->
                    c (VEnv (v1 :: v2s)) (VArgs (vs_out1) :: s) t1 m1
                  end
                ) (VArgs (vs_out2) :: VEnv (v2s) :: s2) t2 m2
          ) (VArgs (vs_out) :: s) t m
      end
    | _ -> failwith "f6s: vs_out is missing"

and ret c v s t m = match s with
  VArgs (vs_out) :: s ->
    begin match vs_out with (* expanding CRet (c) *)
        [] -> c v (VArgs (vs_out) :: s) t m
      | first :: rest -> apply6 v first rest c (VArgs (vs_out) :: s) t m
    end
  | _ -> failwith "ret: vs_out is missing"

and f6t e xs vs c s t m = match s with
  VArgs (vs_out) :: s ->
    begin match e with
        Num (n) -> ret c (VNum (n)) (VArgs (vs_out) :: s) t m
      | Var (x) -> ret c (List.nth vs (Env.offset x xs)) (VArgs (vs_out) :: s) t m
      | Op (e0, op, e1) ->
        f6 e1 xs vs (fun v1 (VArgs (vs_out') :: s1) t1 m1 ->
            f6 e0 xs vs (fun v0 (VArgs (vs_out) :: s0) t0 m0 ->
                begin match s0 with
                    v1 :: s0 ->
                    begin match (v0, v1) with
                        (VNum (n0), VNum (n1)) ->
                        begin match op with
                            Plus -> ret c (VNum (n0 + n1)) (VArgs (vs_out) :: s0) t0 m0
                          | Minus -> ret c (VNum (n0 - n1)) (VArgs (vs_out) :: s0) t0 m0
                          | Times -> ret c (VNum (n0 * n1)) (VArgs (vs_out) :: s0) t0 m0
                          | Divide ->
                            if n1 = 0 then failwith "Division by zero"
                            else ret c (VNum (n0 / n1)) (VArgs (vs_out) :: s0) t0 m0
                        end
                      | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                                        ^ " are not numbers")
                    end
                  | _ -> failwith "stack error op1"
                end) (VArgs (vs_out') :: v1 :: s1) t1 m1
            ) (VArgs (vs_out) :: s) t m
      | Fun (x, e) ->
        begin match vs_out with
            [] -> c (VFun (fun v v2s c' s' t' m' ->
                    f6t e (x :: xs) (v :: vs) c' (VArgs (v2s) :: s') t' m'))
                    (VArgs (vs_out) :: s) t m (* todo: ここの vs_out 捨てる。Applyする時に1つ余計に push されているから辻褄あう *)
          | first :: rest -> f6t e (x :: xs) (first :: vs) c (VArgs (rest) :: s) t m
        end
      | App (e0, e1, e2s) ->
        f6st e2s xs vs (* expanding CApp2 (e0, e1, xs, c) *)
          (fun (VEnv v2s) (VArgs (vs_out2) :: s2s) t2s m2s ->
              f6 e1 xs vs (* expanding CApp1 (e0, xs, c) *)
                (fun v1 (VArgs (vs_out1) :: s1) t1 m1 ->
                  begin match s1 with VEnv (v2s) :: s ->
                    f6 e0 xs vs (* expanding CApp0 (c) *)
                      (fun v0 (VArgs (vs_out0) :: s0) t0 m0 ->
                        begin match s0 with v1 :: VEnv (v2s) :: s ->
                          apply6 v0 v1 v2s c (VArgs (vs_out0) :: s) t0 m0 (* todo: v2s, vs_out, s の順番で積む *)
                        end
                      ) (VArgs (vs_out1) :: v1 :: VEnv (v2s) :: s) t1 m1
                  end
                ) (VArgs (vs_out2) :: VEnv (v2s) :: s2s) t2s m2s
          ) (VArgs (vs_out) :: s) t m
      | Shift (x, e) -> f6 e (x :: xs) (VContS (c, s, t) :: vs) idc [VArgs (vs_out)] TNil m
      | Control (x, e) -> f6 e (x :: xs) (VContC (c, s, t) :: vs) idc [VArgs (vs_out)] TNil m
      | Shift0 (x, e) ->
        begin match m with
            MCons ((c0, s0, t0), m0) ->
            f6 e (x :: xs) (VContS (c, s, t) :: vs) c0 (VArgs (vs_out) :: s0) t0 m0
          | _ -> failwith "shift0 is used without enclosing reset"
        end
      | Control0 (x, e) ->
        begin match m with
            MCons ((c0, s0, t0), m0) ->
            f6 e (x :: xs) (VContC (c, s, t) :: vs) c0 (VArgs (vs_out) :: s0) t0 m0
          | _ -> failwith "control0 is used without enclosing reset"
        end
      | Reset (e) -> f6 e xs vs idc [VArgs (vs_out)] TNil (MCons ((c, s, t), m))
      end
    | _ -> failwith "f6t: vs_out is missing"
and f6st e2s xs vs c s t m = match s with
  VArgs (vs_out) :: s ->
    begin match e2s with
        [] -> c (VEnv vs_out) (VArgs (vs_out) :: s) t m
      | first :: rest ->
        f6st rest xs vs (* expanding CAppS1 (first, xs, c) *)
          (fun (VEnv v2s) (VArgs (vs_out2) :: s2) t2 m2 ->
              f6 first xs vs (* expanding CAppS0 (c) *)
                (fun v1 (VArgs (vs_out1) :: s1) t1 m1 ->
                  begin match s1 with VEnv (v2s) :: s ->
                    c (VEnv (v1 :: v2s)) (VArgs (vs_out1) :: s) t1 m1
                  end
                ) (VArgs (vs_out2) :: VEnv (v2s) :: s2) t2 m2
          ) (VArgs (vs_out) :: s) t m
    end
  | _ -> failwith "f6st: vs_out is missing"

(* apply6 : v -> v -> v list -> c -> s -> t -> m -> v *)
and apply6 v0 v1 v2s c s t m = match s with
  VArgs (vs_out) :: s ->
    begin match v0 with
        VFun (f) -> f v1 v2s c s t m
        (* todo: v2s を s の上に積む。vs_out の変換とは別にする？eval4c のように新たなディレクトリ作る？ *)
      | VContS (c', s', t') -> c' v1 s' t' (MCons ((c, s, t), m))
      | VContC (c', s', t') ->
        c' v1 s' (apnd t' (cons (fun v t m -> c v (VArgs (vs_out) :: s) t m) t)) m
      | _ -> failwith (to_string v0
                        ^ " is not a function; it can not be applied.")
      end
  | _ -> failwith "apply6: vs_out is missing"

(* f : e -> v *)
let f expr = f6 expr [] [] idc [VArgs ([])] TNil MNil
