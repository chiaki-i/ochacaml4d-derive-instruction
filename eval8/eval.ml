open Syntax
open Value

(* Interpreter using combinators factored as instructions : eval8 *)
(* 見た目は ZINC instruction、インライン展開して eval7 になれば良い。>> が肝。*)

(* initial continuation : s -> t -> m -> v *)
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
  | _ -> failwith "stack error: idc"

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (fun v t' m -> h v (cons h' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* (>>) : i -> i -> i *)
let (>>) i0 i1 =
  fun vs c a s t m -> i0 vs (fun v' s' t' m' -> i1 vs c v' s' t' m') a s t m

(* push : i *)
let push = fun vs c a s t m -> c a (a :: s) t m

(* num : int -> i *)
let num n = fun vs c a s t m -> c (VNum (n)) s t m

(* access : int -> i *)
let access n = fun vs c a s t m -> c (List.nth vs n) s t m

(* cur : i -> i *)
let cur i = fun vs c a s t m ->
    let vfun = VFun (fun v vs_out c' s' t' m' ->
            i (v :: vs) (* vs_out *) c' v s' t' m' (* TODO: vs_out を入れる *)
        ) in
    c vfun s t m

(* let cur i = fun c s t m -> match s with *)

(*


(* return : i *)
(* スタックの先頭に積まれたリストが空だったら Pushmark に相当すると考える *)
(* apply7 でうまく実装されているのではないか？ *)
(* VK は返り番地を積んでいるが、ZINC に合わせるためには、無くしてもいいかも？ *)
let return v = fun c s t m -> failwith "not implemented"
(*   match s with
      (VEnv (vs_out) :: s) -> match vs_out with
          [] -> c v s t m
        | first :: rest -> apply6 v first rest c s t m (* TODO: apply6 相当の instruction *)
    | _ -> failwith "stack error: return: missing vs_out" *)
(* let return = fun _ s t m -> match s with
    v :: VK (c) :: s -> c (v :: s) t m
  | _ -> failwith "stack error: return" *)

(* push_env : i *)
let push_env = fun c s t m -> match s with
    VEnv (vs) :: s -> c (VEnv (vs) :: VEnv (vs) :: s) t m
  | _ -> failwith "stack error: push_env"

(* pop_env : i *)
(* 先頭に来ていない env を1番目に持ってくることで、次の instruction で Pop できるようにする *)
let pop_env = fun c s t m -> match s with
    v :: VEnv (vs) :: s -> c (VEnv (vs) :: v :: s) t m
  | _ -> failwith "stack error: pop_env"
*)

(* operation : op -> i *)
let operation op = fun vs c v0 s t m -> match s with
    v1 :: s ->
    begin match (v0, v1) with
        (VNum (n0), VNum (n1)) ->
        begin match op with
            Plus -> c (VNum (n0 + n1)) s t m
          | Minus -> c (VNum (n0 - n1)) s t m
          | Times -> c (VNum (n0 * n1)) s t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else c (VNum (n0 / n1)) s t m
        end
      | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                       ^ " are not numbers")
    end
  | _ -> failwith "stack error: op"

(*
(* call : i *)
(* apply7 に相当する *)
let call = fun vs_out c s t m -> match s with
    v1 :: v0 :: s -> (* 関数が v0、引数の v1 が複数になりうる *)
    begin match v0 with
        VFun (f) -> f vs_out idc (v1 :: s) t m
      | VContS (c', s', t') -> c' (v1 :: s') t' (MCons ((c, s, t), m))
      | VContC (c', s', t') ->
        c' (v1 :: s') (apnd t' (cons (fun v t m -> c (v :: s) t m) t)) m
      | _ -> failwith (to_string v0
                       ^ " is not a function; it can not be applied.")
    end
  | _ -> failwith "stack error: call"

(* shift : i -> i *)
let shift i = fun c s t m -> match s with
    VEnv (vs) :: s -> i idc (VEnv (VContS (c, s, t) :: vs) :: []) TNil m
  | _ -> failwith "stack error: shift"

(* control : i -> i *)
let control i = fun c s t m -> match s with
    VEnv (vs) :: s -> i idc (VEnv (VContC (c, s, t) :: vs) :: []) TNil m
  | _ -> failwith "stack error: control"

(* shift0 : i -> i *)
let shift0 i = fun c s t m -> match s with
    VEnv (vs) :: s ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        i c0 (VEnv (VContS (c, s, t) :: vs) :: s0) t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | _ -> failwith "stack error: shift0"

(* control0 : i -> i *)
let control0 i = fun c s t m -> match s with
    VEnv (vs) :: s ->
    begin match m with
        MCons ((c0, s0, t0), m0) ->
        i c0 (VEnv (VContC (c, s, t) :: vs) :: s0) t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | _ -> failwith "stack error: control0"

(* reset : i -> i *)
let reset i = fun c s t m -> match s with
    VEnv (vs) :: s -> i idc (VEnv (vs) :: []) TNil (MCons ((c, s, t), m))
  | _ -> failwith "stack error: reset"

(* pushmark: (特に f8 において) vs_out が空であるという情報を積む *)
(* ここで、vs_out のことを指す *)
let pushmark i = fun c s t m ->
  let vs_out = [] in
  c vs_out s t m (* vs_out が空であると決め打ちにする *)
*)

(* f8 : e -> string list -> i *)
let rec f8 e xs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.offset x xs)
  | Op (e0, op, e1) ->
    f8 e1 xs >> push >> f8 e0 xs >> operation (op)
  | Fun (x, e) -> cur (f8 e (x :: xs)) (* TODO: あとで f8 を f8t に直す *)
  | _ -> failwith "not implemented"
  (* | App (e0, e1) -> push_env >> (f8 e0 xs) >> pop_env >> (f8 e1 xs) >> call *)
  (* | App (e0, e1, e2s) -> *)
    (* vs_out をこの式の中で使うとして、>> の前後で変数の中身はどのように変化するのだろうか *)
    (* pushmark >> (f8s e2s xs vs) >> (f8 e1 xs vs) >> (f8 e0 xs vs) >> apply *)
    (* (f8s (e2s @ e1) xs vs) >> (f8 e0 xs vs) >> call とすれば、f8s で何もしない instruction を防げる *)
    (* が、これまでの流れに逆行している気もする… *)
    (*
  | Shift (x, e) -> shift (f8 e (x :: xs) vs)
  | Control (x, e) -> control (f8 e (x :: xs) vs)
  | Shift0 (x, e) -> shift0 (f8 e (x :: xs) vs)
  | Control0 (x, e) -> control0 (f8 e (x :: xs) vs)
  | Reset (e) -> reset (f8 e xs vs)
 *)
(* f8s : e -> string list -> env -> i *)
(* and f8s es xs vs = match es with
    [] -> failwith "not implemented"
    (* 何もしない no-op instruction (Pushmark) を作成するのも一つの手かもしれない… *)
    (* c に直接渡す c s t m と書きたいが c を持っていない*)
  | first :: rest ->
    (f8s rest xs vs) >> (f8 first xs vs)
  (* failwith "not implemented" *)

and f8t e xs vs = match e with
    Num (n) -> num n
  | Var (x) -> access (Env.offset x xs)
  | Op (e0, op, e1) -> (* コンパイラ規則の prim に相当する *)
    (f8 e1 xs vs) >> (f8 e0 xs vs) >> operation (op) >> return (* op は1つのバージョンで、後ろに return をつけるかどうかで区別したい *)
  | Fun (x, e) -> grab ((f8 e (x :: xs) vs) >> return)
  (* | App (e0, e1) -> push_env >> (f8 e0 xs) >> pop_env >> (f8 e1 xs) >> call *)
  | App (e0, e1, e2s) ->
    (f8s e2s xs vs) >> (f8 e1 xs vs) >> (f8 e0 xs vs) >> appterm
  | Shift (x, e) -> shift (f8 e (x :: xs) vs)
  | Control (x, e) -> control (f8 e (x :: xs) vs)
  | Shift0 (x, e) -> shift0 (f8 e (x :: xs) vs)
  | Control0 (x, e) -> control0 (f8 e (x :: xs) vs)
  | Reset (e) -> reset (f8 e xs vs)

and f8st e xs vs vs_out = fun c s t m -> match e with
    [] -> cs vs_out s t m
  | first :: rest -> (f8st rest xs vs vs_out) >> (f8 first xs vs)
    (* TODO: call 的なものとして、CAppS0 に相当するものが必要 *)
*)

(* f : e -> v *)
let f expr = f8 expr [] [] idc (VNum 7) [] TNil MNil
