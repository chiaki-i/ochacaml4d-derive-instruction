(* 状態モナドの get してから put (s + 1)。古い状態がそのまま結果になる。 *)
(* state-monad-get と同じく reset がトップレベル App の演算子位置にあるため、 *)
(* eval1b_7 時点では reset を跨ぐ Grab も、k の実行中の Grab も発火しない *)
(reset ((fun v -> fun s -> v) (shift k -> fun s -> k s (s + 1)))) 10
