open Syntax
open Value

(* introduce the Grab that crosses a reset, in f_id : eval1b_7 *)
(* 限定継続 k を複数引数で呼ぶ (k e1 e2 ...) と、app の VContS / VContC ケース
     | VContS (c', t') -> c' v1 t' (MCons ((c, v2s', t), m))
   により、2 つめ以降の引数 v2s' は k の実行が終わるまで m のフレームで待つ。
   k の本体（= reset 本体の残り）の末尾が Fun だったとき、現状では
     closure を作る → idc → m を pop → app_s → closure を壊して束縛
   という往復が起きている。この往復を Grab 一つにまとめたい。

   Grab してよいのは「この式の値がそのまま一番内側の reset の値になる」とき、
   つまり c = idc かつ t = TNil のときに限られる。eval1b_6 で導入した f_id は
   この条件を静的に持つ特殊版であり、Fun ケースで m の先頭フレームを覗いて
   Grab してよい。このステップでは、その f_id の Fun ケースをインライン展開する。
   展開に使うのは idc / app_s / app の定義展開と β 簡約だけで、f / f_t には
   一切手を入れない。 *)

(* cons : h -> t -> t *)
let cons h t = match t with
    TNil -> Trail (h)
  | Trail (h') -> Trail (Append (h, h'))

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (h) -> cons h t1

(* run_h : h -> v -> t -> m -> v *)
let rec run_h h v t m = match h with
    Hold (v2s, c) -> app_s v v2s c t m (* 非関数化したことで app_s がこちらに移動 *)
  | Append (h, h') -> run_h h v (cons h' t) m

(* initial continuation : v -> t -> m -> v *)
(* MCons の非関数化にあたり、ここで app_c0 を作り直す *)
and idc v t m = match t with
    TNil ->
    begin match m with
        MNil -> v
      | MCons ((c0, v2s, t), m) ->
        let app_c0 = fun v0 t0 m0 -> app_s v0 v2s c0 t0 m0 in
        app_c0 v t m
    end
  | Trail (h) -> run_h h v TNil m

(* f : definitional interpreter *)
(* f : e -> string list -> v list -> c -> t -> m -> v *)
and f e xs vs c t m =
  match e with
    Num (n) -> c (VNum (n)) t m
  | Var (x) -> c (List.nth vs (Env.offset x xs)) t m
  | Op (e0, op, e1) ->
    f e1 xs vs (fun v1 t0 m0 ->
        f e0 xs vs (fun v0 t1 m1 ->
            begin match (v0, v1) with
                (VNum (n0), VNum (n1)) ->
                begin match op with
                    Plus -> c (VNum (n0 + n1)) t1 m1
                  | Minus -> c (VNum (n0 - n1)) t1 m1
                  | Times -> c (VNum (n0 * n1)) t1 m1
                  | Divide ->
                    if n1 = 0 then failwith "Division by zero"
                    else c (VNum (n0 / n1)) t1 m1
                end
              | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                               ^ " are not numbers")
            end) t0 m0) t m
  | Fun (x, e) ->
    c (VFun (fun v1 v2s' c' t' m' ->
              f_t e (x :: xs) (v1 :: vs) v2s' c' t' m')) t m
  | App (e0, e2s) ->
    f_s e2s xs vs (fun v2s t2 m2 ->
      f e0 xs vs (fun v0 t0 m0 ->
        app_s v0 v2s c t0 m0) t2 m2) t m
  (* shift / control / reset は、本体を idc・TNil の下で走らせる。
     これは f_id の定義 f_id e xs vs m = f e xs vs idc TNil m そのものなので、
     (f の代わりに) f_id を呼び出す。捕捉する継続 VContS (c, t) や
     m に積むフレーム (c, [], t) は f 側の c / t なのでそのまま残る。 *)
  | Shift (x, e) -> f_id e (x :: xs) (VContS (c, t) :: vs) m
  | Control (x, e) -> f_id e (x :: xs) (VContC (c, t) :: vs) m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          f_t e (x :: xs) (VContS (c, t) :: vs) v2s c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          f_t e (x :: xs) (VContC (c, t) :: vs) v2s c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f_id e xs vs (MCons ((c, [], t), m))

(* f_t : e -> string list -> v list -> v list -> c -> t -> m -> v *)
and f_t e xs vs v2s' c t m =
  let app_c = fun v t m -> app_s v v2s' c t m in
  match e with
    Num (n) -> app_c (VNum (n)) t m
  | Var (x) -> app_c (List.nth vs (Env.offset x xs)) t m
  | Op (e0, op, e1) ->
    f e1 xs vs (fun v1 t0 m0 ->
        f e0 xs vs (fun v0 t1 m1 ->
            begin match (v0, v1) with
                (VNum (n0), VNum (n1)) ->
                begin match op with
                    Plus -> app_c (VNum (n0 + n1)) t1 m1
                  | Minus -> app_c (VNum (n0 - n1)) t1 m1
                  | Times -> app_c (VNum (n0 * n1)) t1 m1
                  | Divide ->
                    if n1 = 0 then failwith "Division by zero"
                    else app_c (VNum (n0 / n1)) t1 m1
                end
              | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                               ^ " are not numbers")
            end) t0 m0) t m
  | Fun (x, e) ->
    app_c (VFun (fun v1 v2s' c' t' m' ->
              f_t e (x :: xs) (v1 :: vs) v2s' c' t' m')) t m
  | App (e0, e2s) ->
    f_s e2s xs vs (fun v2s t2 m2 ->
      f e0 xs vs (fun v0 t0 m0 ->
        app_s v0 v2s (fun v t m -> app_s v v2s' c t m) t0 m0) t2 m2) t m
        (* app_s v0 v2s app_c t0 m0) t2 m2) t m *)
  (* f と同じく、f の代わりに f_id を呼び出す *)
  | Shift (x, e) -> f_id e (x :: xs) (VContS (app_c, t) :: vs) m
  | Control (x, e) -> f_id e (x :: xs) (VContC (app_c, t) :: vs) m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          f_t e (x :: xs) (VContS (app_c, t) :: vs) v2s c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          f_t e (x :: xs) (VContC (app_c, t) :: vs) v2s c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f_id e xs vs (MCons ((c, v2s', t), m))

(* f_id : e -> string list -> v list -> m -> v *)
(* f_id e xs vs m = f e xs vs idc TNil m

   f に c := idc, t := TNil を代入しただけのもの。c と t が引数から消える。
   「この式の値は、そのまま一番内側の reset の値になる」位置を表す。
   したがって m の先頭フレーム (c0, v2s, t0) の v2s は
   「この reset の結果に適用されるべき引数列」であり、Fun ケースを展開すると
   そこから直接 Grab できる。

   各ケースは f の形をそのまま保ち、c を idc に、t を TNil に置き換えただけ。
   ただし部分式（Op の e0 / e1、App の e2s）は非末尾なので f のまま呼ぶ。
   非末尾から戻ってくる継続は動的な t1 / m1 を受け取るため TNil に固定できず、
   そこでは idc をそのまま適用する。 *)
and f_id e xs vs m =
  match e with
    Num (n) -> idc (VNum (n)) TNil m
  | Var (x) -> idc (List.nth vs (Env.offset x xs)) TNil m
  | Op (e0, op, e1) ->
    f e1 xs vs (fun v1 t0 m0 ->
        f e0 xs vs (fun v0 t1 m1 ->
            begin match (v0, v1) with
                (VNum (n0), VNum (n1)) ->
                begin match op with
                    (* 戻ってきた時点の t1 は TNil とは限らないので idc を適用する *)
                    Plus -> idc (VNum (n0 + n1)) t1 m1
                  | Minus -> idc (VNum (n0 - n1)) t1 m1
                  | Times -> idc (VNum (n0 * n1)) t1 m1
                  | Divide ->
                    if n1 = 0 then failwith "Division by zero"
                    else idc (VNum (n0 / n1)) t1 m1
                end
              | _ -> failwith (to_string v0 ^ " or " ^ to_string v1
                               ^ " are not numbers")
            end) t0 m0) TNil m
  (* idc (VFun F) TNil m を展開する。

       idc (VFun F) TNil m
     = match m with                                      (idc の TNil ケース)
         MNil -> VFun F
       | MCons ((c0, v2s, t0), m0) -> app_s (VFun F) v2s c0 t0 m0
     = match m with
         MNil -> VFun F
       | MCons ((c0, [], t0), m0) -> c0 (VFun F) t0 m0    (app_s の [] ケース)
       | MCons ((c0, v1 :: v2s, t0), m0) ->
           app (VFun F) v1 v2s c0 t0 m0                   (app_s の :: ケース)
         = F v1 v2s c0 t0 m0                              (app の VFun ケース)
         = f_t e (x :: xs) (v1 :: vs) v2s c0 t0 m0        (β)

     最後の行が Grab である。reset の外で待っている引数 v1 を、closure を
     作らずにそのまま x に束縛して本体に入る。
     m が MNil のとき、および先頭フレームの引数列が空のときは、
     これまで通り closure を作って idc に渡す。 *)
  | Fun (x, e) ->
    begin match m with
        MCons ((c0, v1 :: v2s, t0), m0) ->
          f_t e (x :: xs) (v1 :: vs) v2s c0 t0 m0
      | _ ->
        idc (VFun (fun v1 v2s' c' t' m' ->
                f_t e (x :: xs) (v1 :: vs) v2s' c' t' m')) TNil m
    end
  (* f の App ケースに c := idc を代入しただけ（f_id e xs vs m = f e xs vs idc TNil m
     という定義そのものの展開）。 *)
  | App (e0, e2s) ->
    f_s e2s xs vs (fun v2s t2 m2 ->
      f e0 xs vs (fun v0 t0 m0 ->
        app_s v0 v2s idc t0 m0) t2 m2) TNil m
  (* c = idc, t = TNil なので、捕捉される継続は VContS (idc, TNil) になる。*)
  | Shift (x, e) -> f_id e (x :: xs) (VContS (idc, TNil) :: vs) m
  | Control (x, e) -> f_id e (x :: xs) (VContC (idc, TNil) :: vs) m
  | Shift0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          f_t e (x :: xs) (VContS (idc, TNil) :: vs) v2s c0 t0 m0
      | _ -> failwith "shift0 is used without enclosing reset"
    end
  | Control0 (x, e) ->
    begin match m with
        MCons ((c0, v2s, t0), m0) ->
          f_t e (x :: xs) (VContC (idc, TNil) :: vs) v2s c0 t0 m0
      | _ -> failwith "control0 is used without enclosing reset"
    end
  | Reset (e) -> f_id e xs vs (MCons ((idc, [], TNil), m))

(* f_s : e list -> string list -> v list -> c -> t -> m -> v list *)
and f_s e2s xs vs c t m = match e2s with
    [] -> c [] t m
  | e :: e2s ->
    f_s e2s xs vs (fun v2s t2 m2 ->
      f e xs vs (fun v1 t1 m1 ->
        c (v1 :: v2s) t1 m1) t2 m2) t m

(* app : v -> v -> v list -> c -> t -> m -> v *)
and app v0 v1 v2s' c t m =
  match v0 with
    VFun (f) -> f v1 v2s' c t m
  (* k を複数引数で呼んだときの 2 つめ以降の引数 v2s' は、ここで m のフレームに
     積まれ、k の実行が終わるまで待つ。この v2s' を k の末尾で Grab するのが
     f_id の目的である。 *)
  | VContS (c', t') -> c' v1 t' (MCons ((c, v2s', t), m))
  (* | VContC (c', t') -> c' v1 (apnd t' (cons app_c t)) m *)
  | VContC (c', t') -> c' v1 (apnd t' (cons (Hold (v2s', c)) t)) m
  | _ -> failwith (to_string v0
                   ^ " is not a function; it can't be applied.")

(* app_s : v -> v list -> c -> t -> m -> v *)
and app_s v0 v2s c t m = match v2s with
    [] -> c v0 t m
  | v1 :: v2s -> app v0 v1 v2s c t m

(* f_init : e -> v *)
let f_init expr = f expr [] [] idc TNil MNil
