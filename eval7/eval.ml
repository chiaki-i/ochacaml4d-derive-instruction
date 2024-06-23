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

(* f7 : e -> string list -> c -> s -> t -> m -> v *)
let rec f7 e xs c s t m = match s with
    VEnv (vs) :: s ->
    begin match e with
        Num (n) -> c (VNum (n) :: s) t m
      | Var (x) -> c ((List.nth vs (Env.offset x xs)) :: s) t m
      | Op (e0, op, e1) ->
        f7 e1 xs (fun s1 t1 m1 ->
            begin match s1 with
                v1 :: VEnv (vs) :: s1 -> (* VNum を Stack から取り出す *)
                f7 e0 xs (fun s0 t0 m0 ->
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
                    end) (VEnv (vs) :: v1 :: s1) t1 m1 (* f7 呼び出しのために一時的に vs を積む *)
              | _ -> failwith "stack error"
            end) (VEnv (vs) :: VEnv (vs) :: s) t m (* f7 呼び出しのために一時的に vs を積む *)
      | Fun (x, e) ->
        let vfun = VFun (fun c' s' t' m' ->
            begin match s' with
                v :: s' -> f7 e (x :: xs) c' (VEnv (v :: vs) :: s') t' m'
              | _ -> failwith "stack error"
            end) in
        c (vfun :: s) t m
      | App (e0, e1, e2s) ->
        f7s e2s xs (* vs *)
          (fun s2s t2s m2s ->
            begin match s2s with VEnv (v2s) :: VEnv (vs) :: s -> (* v2s : v list *)
              f7 e1 xs (* vs *)
                (fun s1 t1 m1 ->
                  begin match s1 with v1 :: VEnv (v2s) :: VEnv (vs) :: s -> (* v1 : v *)
                    f7 e0 xs (* vs *)
                      (fun s0 t0 m0 ->
                        begin match s0 with v0 :: VEnv (v1 :: v2s) :: s -> (* v0 : v *)
                          apply7 v0 v1 v2s c s t0 m0
                        end
                      ) (VEnv (vs) :: VEnv (v1 :: v2s) :: s) t1 m1 (* f7 呼び出しのために一時的に vs を積む *)
                  end
                ) (VEnv (vs) :: VEnv (v2s) :: VEnv (vs) :: s) t2s m2s
            end
          ) (VEnv (vs) :: VEnv (vs) :: s) t m (* f7s 呼び出しのために一時的に vs を積む *)
      | Shift (x, e) ->
        f7 e (x :: xs) idc (VEnv (VContS (c, s, t) :: vs) :: []) TNil m
      | Control (x, e) ->
        f7 e (x :: xs) idc (VEnv (VContC (c, s, t) :: vs) :: []) TNil m
      | Shift0 (x, e) ->
        begin match m with
            MCons ((c0, s0, t0), m0) ->
            f7 e (x :: xs) c0 (VEnv (VContS (c, s, t) :: vs) :: s0) t0 m0
          | _ -> failwith "shift0 is used without enclosing reset"
        end
      | Control0 (x, e) ->
        begin match m with
            MCons ((c0, s0, t0), m0) ->
            f7 e (x :: xs) c0 (VEnv (VContC (c, s, t) :: vs) :: s0) t0 m0
          | _ -> failwith "control0 is used without enclosing reset"
        end
      | Reset (e) -> f7 e xs idc (VEnv (vs) :: []) TNil (MCons ((c, s, t), m))
    end
  | _ -> failwith "f7: stack error"
(* f7s: e list -> string list -> s -> t -> m *)
and f7s es xs c s t m = match s with
    VEnv (vs) :: s ->
      begin match es with
        [] -> c (VEnv ([]) :: s) t m
      | first :: rest ->
        f7s rest xs (* vs *)
          (fun s1 t1 m1 ->
            begin match s1 with VEnv (v1) :: VEnv (vs) :: s ->
              f7 first xs (* vs *)
                (fun s2 t2 m2 ->
                  begin match s2 with v2 :: VEnv (v2s) :: s ->
                    c (VEnv (v2 :: v2s) :: s) t2 m2 (* v2 :: VEnv (v2s) :: s にしなくて良いか検証 *)
                  end
                ) (VEnv (vs) :: VEnv (v1) :: s) t1 m1 (* f7 呼び出しのために一時的に vs を積む *)
            end
          ) (VEnv (vs) :: VEnv (vs) :: s) t m (* f7s 呼び出しのために一時的に vs を積む *)
      end
    | _ -> failwith "f7s: stack error"
(* apply7 : v -> v -> v list -> c -> s -> t -> m -> v *)
and apply7 v0 v1 v2s c s t m =
  app7 v0 v1 (fun (v2 :: VEnv (v2s) :: s2) t2 m2 ->
    begin match v2s with
        [] -> c (v2 :: s2) t2 m2
      | first :: rest -> apply7 v2 first rest c s2 t2 m2
    end
    ) (VEnv (v2s) :: s) t m
  (* match v2s with
    [] -> app7 v0 v1 c s t m
  | first :: rest ->
    app7 v0 v1
      (fun s2 t2 m2 ->
        begin match s2 with v2 :: VEnv (first :: rest) :: s' ->
          apply7 v2 first rest c s' t2 m2
        end
      ) (VEnv (first :: rest) :: s) t m *)
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
let f expr = f7 expr [] idc (VEnv ([]) :: []) TNil MNil
