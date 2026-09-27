(* 状態モナドの get : reset ((fun v -> fun s -> v) M) s0 が run_state にあたる *)
(* shift k -> fun s -> k s s が get。k を 2 引数で呼ぶので、2 つめの s は k の *)
(* 実行中ずっとメタ継続のフレームで待つ。reset がトップレベルの App の演算子 *)
(* 位置にあるため（(reset ...) 7 の形）、eval1b_7 時点ではこの引数への Grab は *)
(* 一切発火しない（詳細は README の 1b_7 の説明を参照） *)
(reset ((fun v -> fun s -> v) (shift k -> fun s -> k s s))) 7
