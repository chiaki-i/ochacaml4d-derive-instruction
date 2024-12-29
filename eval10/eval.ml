open Syntax
open Value

(* Interpreter with linear instructions : eval10 *)

(* cons : h -> t -> t *)
let cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (Append (h, h'))

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

let idc = []

(* run_h10 : h -> v -> t -> m -> v *)
let rec run_h10 h vs v t m = match h with
    Hold (c, s) -> run_c10 c vs (v :: s) t m
  | Append (h, h') -> run_h10 h vs v (cons h' t) m

(* run_c10 : c -> s -> t -> m -> v *)
and run_c10 c vs s t m = match (c, s) with
    ([], v :: []) ->
    begin match t with
        TNil ->
        begin match m with
            [] -> v
          | (c0, s0, t0) :: m0 -> run_c10 c0 vs (v :: s0) t0 m0
        end
      | Trail (h) -> run_h10 h vs v TNil m
    end
  | (IVArg :: c, v :: s) -> run_c10 c vs (VArg (v) :: s) t m
  | (IVArg :: c, _) -> failwith "stack error: IVArg"
  | (INum (n) :: c, s) -> run_c10 c vs (VNum (n) :: s) t m
  | (IAccess (n) :: c, s) -> run_c10 c vs ((List.nth vs n) :: s) t m
  | (IOp (op) :: c, v0 :: v1 :: s) ->
    begin match (v0, v1) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> run_c10 c vs (VNum (n0 + n1) :: s) t m
          | Minus -> run_c10 c vs (VNum (n0 - n1) :: s) t m
          | Times -> run_c10 c vs (VNum (n0 * n1) :: s) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c10 c vs (VNum (n0 / n1) :: s) t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                       ^ " are not numbers")
    end
  | (IGrab (i0) :: IApply :: i1, VArg (v1) :: s') ->
    (* print_endline ("grab: " ^ Value.s_to_string s); *)
    run_c10 (i0 @ i1) (v1 :: vs) s' t m
  | (IGrab (c0) :: c1, s) ->
    run_c10 c1 vs (VFun (c0, vs) :: s) t m
  | (IApply :: c1, v0 :: VArg (v1) :: s) ->
    begin match v0 with
        VFun (c0, vs) -> run_c10 (c0 @ c1) (v1 :: vs) s t m
      | VContS (c0, s0, t0) -> run_c10 c0 vs (v1 :: s0) t0 ((c1, s, t) :: m)
      | VContC (c0, s0, t0) ->
        run_c10 c0 vs (v1 :: s0) (apnd t0 (cons (Hold (c1, s)) t)) m
      | _ -> failwith (to_string v0
                       ^ " is not a function; it can not be applied.")
    end
  | (IApply :: c1, _) -> failwith "stack error: IApply"
  | (IShift (i) :: c1, s) ->
    run_c10 i (VContS (c1, s, t) :: vs) [] TNil m
  | (IControl (i) :: c1, s) ->
    run_c10 i (VContC (c1, s, t) :: vs) [] TNil m
  | (IShift0 (i) :: c1, s) ->
    begin match m with
        (c0, s0, t0) :: m0 ->
        run_c10 (i @ c0) (VContS (c1, s, t) :: vs) s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | (IControl0 (i) :: c1, s) ->
    begin match m with
        (c0, s0, t0) :: m0 ->
        run_c10 (i @ c0) (VContS (c1, s, t) :: vs) s0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | (IReset (i) :: c1, s) ->
    run_c10 (i @ idc) vs [] TNil ((c1, s, t) :: m)
  | _ -> failwith (s_to_string s)

(* f10 : e -> string list -> c *)
let rec f10 e xs = match e with
    Num (n) -> [INum (n)]
  | Var (x) -> [IAccess (Env.offset x xs)]
  | Op (e0, op, e1) ->
    (f10 e1 xs) @ (f10 e0 xs) @ [IOp (op)]
  | Fun (x, e) -> [IGrab (f10 e (x :: xs))]
  | App (e0, e1, _) ->
    (f10 e1 xs) @ [IVArg] @ (f10 e0 xs) @ [IApply]
  | Shift (x, e) -> [IShift (f10 e (x :: xs))]
  | Control (x, e) -> [IControl (f10 e (x :: xs))]
  | Shift0 (x, e) -> [IShift0 (f10 e (x :: xs))]
  | Control0 (x, e) -> [IControl0 (f10 e (x :: xs))]
  | Reset (e) -> [IReset (f10 e xs)]

(* f : e -> v *)
let f expr = run_c10 (f10 expr []) [] [] TNil []
