# ochacaml4d-derive-instruction

限定継続演算子のための仮想機械 (DAM) を、definitional interpreter からの
プログラム変換の繰り返しによって導出するリポジトリ。

対応論文: `/Users/chiaki/Documents/git/ochacaml4d.paper/jssst_journal`
（5 節「DAM の導出」= `derivation-overview.tex`, `derivation-step{1,5,8,10}.tex`）

---

## 最重要ルール: 導出は「自明な変換」のみ

**このリポジトリ全体が一種の証明である。** 各フォルダは導出の 1 ステップであり、
隣り合うステップの差分が「正当性の自明な変換」であることが、
step 1a の definitional interpreter と最終的な仮想機械の等価性の根拠になっている
（論文 5 節冒頭: 「導出のステップのうち、step 1d の…実装以外は、すべてのステップが
自明な変換になっている」「非関数化やデータの形の変換など、正当性の自明な機械的な
変換だけを繰り返す」）。

したがって OCaml コードを書くときは、必ず次を守ること。

1. **新しいステップのコードは、一つ前のステップのコードに対する自明な変換としてのみ書く。**
   前のステップの `eval.ml` を必ず読み、そこからの差分として書く。
2. **`make test` を通すために、その場でロジックを考えて書いてはならない。**
   テストが通らないのは、変換が自明でないか、変換をかける順番が間違っているかの
   どちらかである。テストを通すための場当たり的な修正は、証明を壊す。
3. **非自明な追加をしたくなったら、手を止めて相談する。**
   唯一の例外は step 1d（`Appterm` の原形）で、論文自身が「これまでの導出とは異なり、
   意図的に実装を追加している点に注意されたい」と明記している。それ以外に例外はない。
4. 使ってよい変換は限られている ――
   非関数化 (defunctionalization) / 関数化 / データの形の変換 / インライン展開 /
   補題の適用 / コンビネータ化 / 命令列のリスト化。
   commit message には **どの変換をかけたか** を書く。

論文 5.1 の注意: 「どの変換をどの時点でかけるかには任意性があり、その選択によって
最終的に得られる仮想機械は異なってくる」。変換の順序自体が研究の中身なので、
順序を勝手に変えないこと。

## 作業手順（2 コミット制）

`eval8a` から `eval9a` を導出する場合:

1. `cp -r eval8a eval9a`
2. `cd eval9a && make test` が通ることを確認
3. commit（例: `eval9a: derived from eval8a`）… **無変更コピーであることを記録する**
4. プログラム変換を適用（この場合は継続の非関数化）
5. `cd eval9a && make test`
6. commit（何の変換をかけたかを書く）

3 を独立したコミットにすることで、4 の差分＝変換内容そのものになる。この形を崩さない。

## derivation path の調べ方

**フォルダ名を推測しない。** ブランチによって実在するフォルダが違う
（例: main には `eval1d_1/1d_2/1d_3` があるが `eval1d` はない。
`eval1-appterm-meta-optimize` はその逆）。

現ブランチの `README.md` の `## Derivation path` 直下、**最初の `###` セクション**が
そのブランチの最新パス。必ずそれを読んでから着手する。

## ブランチ地図

### "a" パス（Appterm、論文の主線）

| | **main** (= `eval1-appterm-f_st`)【正】 | **eval1-appterm-meta-optimize**【実験】 |
|---|---|---|
| 分岐点 | `c515031`（`eval1-appterm` の tip） | 同左 |
| 前半 | `eval1a → 1b_1 → 1b_2 → 1b_3` | 同じ。ただし **1b_3 で `f_t` 導入と同時に `MCons` を非関数化** |
| Appterm 導入 | `1d_1`（補題適用）→ `1d_2`（`f_st` 導入）→ `1d_3`（`app_s` 展開）の 3 ステップ | **`1d`** — 上記を 1 ステップに圧縮 |
| 後半 | `2a → 4b → 4c → 6a → 8a → 9a → 9c → 10a → 10b → 10c` | 同名。ただし `MCons` が `(c, s, t)` を持つ形に変わる |
| 実験枝 | — | **`eval1e_1`**: `1d` から trail (`cons`) 側も非関数化しようとし `f_sr` を導入したが、`f_t` と併存して冗長になり頓挫（stash `12fe29b` に記録）。パス外 |

`jssst`（2025-12-06）と `eval1-appterm`（2026-06-08）は main に完全包含（0 ahead）。参照不要。
ただし `jssst` は**論文の実装スナップショット**なので、論文と突き合わせるときはこれを見る。

### "st" パス（tail interpreter）

| ブランチ | パス | 状態 |
|---|---|---|
| `eval1-meta-optimize`（2026-07-05） | `1st → 2st → 5st → 5st1 → 7st → 7st1 → 8st → 9st → 10st` | メタ継続 `m` に `(c, s, t)`（裸の継続）を保存し、m-pop 時に `app_c` を**遅延生成**。**最適化済み＝お手本** |
| `eval1-appterm-meta-optimize` | "a" パス | 同じ最適化を "a" パスへ移植中。`(app_c, s, t)` を事前生成していたのを `(c, s, t)` に変える |

TODO メモ `49f7312` は `eval1-meta-optimize` から現ブランチへ cherry-pick 済み（`d02974c`）。
**"a" パスで迷ったら "st" パスの対応するフォルダを見る。**

## 論文 step ↔ フォルダ 対応

`jssst` ブランチが論文（図 `fig:derivation-step-table`）に一致する。

| 論文 step | 内容 | 最適化 | 節 | jssst | main | meta-optimize |
|---|---|---|---|---|---|---|
| 1a | definitional interpreter | | 5.2 | `eval1a` | `eval1a` | `eval1a` |
| 1b | 末尾呼出用インタプリタの導出 | ✓ | 5.2 | `eval1b_{1,2,3}` | 同 | 同 |
| 1c | `Grab` と `Apply` の原形の導出 | ✓ | 5.2 | `eval1c` | `1d_*` に吸収 | `1d` に吸収 |
| **1d** | **末尾の関数適用の最適化実装の挿入 ← 唯一の非自明ステップ** | ✓ | 5.2 | `eval1d` | `eval1d_{1,2,3}` | `eval1d` |
| 2a | 継続の非関数化 | | 5.3 | `eval2a` | `eval2a` | `eval2a` |
| 4a | 引数スタック導入 | | 5.3 | `eval4a` | 廃止 | 廃止 |
| 4b | 各関数クロージャの引数をスタックに積む | ✓ | 5.3 | `eval4b` | `eval4b` | `eval4b` |
| 4c | 計算結果を引数スタックで渡す | | 5.3 | `eval4c` | `eval4c` | `eval4c` |
| 6a | 継続の関数化 | | 5.4 | `eval6a` | `eval6a` | `eval6a` |
| 8a | 継続のコンビネータ化 | | 5.4 | `eval8a` | `eval8a` | `eval8a` |
| 9a | 継続の非関数化 | | 5.5 | `eval9a` | `eval9a` | `eval9a` |
| 9b | 関数抽象とトレイルの非関数化 | | 5.5 | `eval9b` | `eval9c` に統合 | `eval9c` に統合 |
| 10a | 継続を命令のリストとして実装 | | 5.5 | `eval10a` | `eval10a` | `eval10a` |
| 10b | リターンスタック操作の最適化 | ✓ | 5.5 | `eval10b` | `eval10b` | `eval10b` |
| （論文外） | `Appterm` 命令の導入（`Apply` の Return 最適化版） | | — | `eval10c` | `eval10c` | `eval10c` |

論文の step 番号とフォルダ名はブランチによってズレる。**論文を引くときは step 番号、
コードを触るときはフォルダ名**で考え、対応はこの表で引く。

## ビルドとテスト

```bash
cd eval8a && make test    # test-suite/check-vm で 0〜4 を実行（34 tests）
```

- **`make test` は最後に `make clean` を走らせる**（Makefile の test ターゲット）
- 前提: `~/include/OCamlMakefile`（導入済み）、opam の ocaml
- `make` だけなら `./interpreter` が生成される。標準入力にコードを与え Control-D で実行

## ファイル構成（各 eval* フォルダ共通）

`syntax.ml` → `parser.mly` → `lexer.mll` → `env.ml` → `value.ml` → **`eval.ml`** → `main.ml`

導出で触るのは基本 `eval.ml` のみ。`value.ml` は継続や命令の型が変わるステップでのみ触る。
