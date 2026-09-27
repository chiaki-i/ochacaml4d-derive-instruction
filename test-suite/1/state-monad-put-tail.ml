(* state-monad-put と計算内容は同じだが、reset を fun dummy の本体という *)
(* 末尾位置（f_t の Reset ケース経由）に置いた変種。この場合は外側の引数 10 が *)
(* フレームに残り、reset を跨ぐ Grab（1 段階目）は発火する。しかし k s (s + 1) *)
(* で k を 2 引数で呼ぶ側の Grab（2 段階目）は、eval1b_7 では g_t 相当を作って *)
(* いないので発火しない。state-monad-put との対比で、reset の位置と k の *)
(* 引数消費が独立した 2 つの条件であることを確認できる *)
(fun dummy -> reset ((fun v -> fun s -> v) (shift k -> fun s -> k s (s + 1)))) 0 10
