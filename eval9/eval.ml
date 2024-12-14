open Syntax
open Value

(* Defunctionalized interpreter : eval9 *)

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_c9 : c -> s -> t -> m -> v *)
let rec run_c9 c s r t m = match (c, s, r) with
    ([], v :: [], []) ->
    begin match t with
        TNil ->
        begin match m with
            [] -> v
          | (c, s, r, t) :: m -> run_c9 c (v :: s) r t m
        end
      | Trail (h) -> h v TNil m
    end
  | (i1 :: c, v :: s, VEnv (vs) :: r) ->
    run_i9 i1 vs c (v :: s) r t m
  | _ -> failwith "run_c9 unexpected"

(* run_i9 : i -> c -> s -> t -> m -> v *)
and run_i9 i vs c s r t m = match i with
    IVArg ->
    begin match s with (v :: s) ->
        run_c9 c (VArg (v) :: s) r t m
      | _ -> failwith "stack error: run_i9 varg"
    end
  | INum (n) -> run_c9 c (VNum (n) :: s) r t m
  | IAccess (n) -> run_c9 c ((List.nth vs n) :: s) r t m
  | IOp (op) ->
    begin match (s, r) with
        (v0 :: v1 :: s, r) ->
        begin match (v0, v1) with
            (VNum (n0), VNum (n1)) ->
            begin match op with
                Plus -> run_c9 c (VNum (n0 + n1) :: s) r t m
              | Minus -> run_c9 c (VNum (n0 - n1) :: s) r t m
              | Times -> run_c9 c (VNum (n0 * n1) :: s) r t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c9 c (VNum (n0 / n1) :: s) r t m
            end
          | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                           ^ " are not numbers")
        end
      | _ -> failwith "stack error"
    end
  (*
  | ICall ->
    begin match s with
        v1 :: v0 :: s ->
        begin match v0 with
            VFun (i, vs) -> run_i9 i [] (VEnv (v1 :: vs) :: VK (c) :: s) t m
          | VContS (c', s', t') -> run_c9 c' (v1 :: s') t' ((c, s, t) :: m)
          | VContC (c', s', t') ->
            run_c9 c' (v1 :: s') (apnd t' (cons (Hold (c, s)) t)) m
          | _ -> failwith (to_string v0
                          ^ " is not a function; it can not be applied.")
        end
      | _ -> failwith "stack error"
    end
    *)
    (*
    | IShift (i) ->
      begin match s with
          VEnv (vs) :: s ->
          run_i9 i [] (VEnv (VContS (c, s, t) :: vs) :: []) TNil m
        | _ -> failwith "stack error"
      end
    | IControl (i) ->
      begin match s with
          VEnv (vs) :: s ->
          run_i9 i [] (VEnv (VContC (c, s, t) :: vs) :: []) TNil m
        | _ -> failwith "stack error"
      end
    | IShift0 (i) ->
      begin match s with
          VEnv (vs) :: s ->
          begin match m with
              (c0, s0, t0) :: m0 ->
              run_i9 i c0 (VEnv (VContS (c, s, t) :: vs) :: s0) t0 m0
            | _ -> failwith "shift0 is used without enclosing reset"
          end
        | _ -> failwith "stack error"
      end
    | IControl0 (i) ->
      begin match s with
          VEnv (vs) :: s ->
          begin match m with
              (c0, s0, t0) :: m0 ->
              run_i9 i c0 (VEnv (VContC (c, s, t) :: vs) :: s0) t0 m0
            | _ -> failwith "control0 is used without enclosing reset"
          end
        | _ -> failwith "stack error"
      end
    | IReset (i) ->
      begin match s with
          VEnv (vs) :: s ->
          run_i9 i [] (VEnv (vs) :: []) TNil ((c, s, t) :: m)
        | _ -> failwith "stack error"
      end *)
  | ISeq (i0, i1) ->
    run_i9 i0 vs (i1 :: c) s (VEnv (vs) :: r) t m
  | _ -> failwith "not implemented"

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = ISeq (i0, i1)

(* f9 : e -> string list -> i *)
let rec f9 e xs = begin match e with
    Num (n) -> INum (n)
  | Var (x) -> IAccess (Env.offset x xs)
  | Op (e0, op, e1) ->
    (f9 e0 xs) >> (f9 e1 xs) >> IOp (op)
  (*
  | Fun (x, e) -> IPush_closure ((f9 e (x :: xs)) >> IReturn)
  | App (e0, e1) -> IPush_env >> (f9 e0 xs) >> IPop_env >> (f9 e1 xs) >> ICall
  | Shift (x, e) -> IShift (f9 e (x :: xs))
  | Control (x, e) -> IControl (f9 e (x :: xs))
  | Shift0 (x, e) -> IShift0 (f9 e (x :: xs))
  | Control0 (x, e) -> IControl0 (f9 e (x :: xs))
  | Reset (e) -> IReset (f9 e xs)
  *)
  | _ -> failwith "not implemented"
  end

(* f : e -> v *)
let f expr = run_i9 (f9 expr []) [] [] [] [] TNil []
