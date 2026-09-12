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
5. **型を変える変換（例: `MCons` や `Trail` の非関数化）は、それより下流にある
   既存フォルダの `eval.ml`/`value.ml` にも波及する。** その場合は新規フォルダを
   作るのではなく、既存フォルダを直接編集して型変化を伝播させる（本ブランチの
   `2d3fae2`, `54dad61`, `dbdec63` を参照）。この波及コミットも「どの変換の
   伝播か」を明記する。

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
（型の波及のように新規フォルダを作らない変換の場合は、この 2 コミット制の対象外。
上のルール 5 に従う。）

## derivation path の調べ方

**フォルダ名を推測しない。** ブランチによって実在するフォルダが違う
（例: 本ブランチ・main には `eval1d_1/1d_2/1d_3` があるが `eval1d` はない。
`eval1-appterm`/`eval1-appterm-meta-optimize` はその逆で `eval1d` を持つ）。

現ブランチの `README.md` の `## Derivation path` 直下、**最初の `###` セクション**が
そのブランチの最新パス。必ずそれを読んでから着手する
（`SessionStart` フックが `[path]` として自動的に注入するが、フォルダの中身までは
読んでいないので、着手前に自分でも `README.md` を確認すること）。

## ブランチ地図

### "a" パス（Appterm、論文の主線）

本ブランチ `eval1-appterm-f_st-meta-optimize` は現在 **main と同一コミット**
（`main` に対して 0 ahead / 0 behind）。つまりここが "a" パスの最新かつ正系。

```
eval1-appterm (c515031, Journal revision)
  ├─ eval1-appterm-f_st (32cf0d4)   … eval1d を 1d_1/1d_2/1d_3 の3ステップに分解（f_st 導入）、
  │                                    続く 2a〜10c も f_st ベースで全部再導出
  │    └─ eval1-appterm-f_st-meta-optimize (= main, 本ブランチ)
  │         … 1b_4/1b_5 で MCons・Trail を非関数化し、"st" パスの最適化を "a" パスへ移植
  └─ eval1-appterm-meta-optimize（兄弟枝・別解、c515031 から直接分岐）
       … eval1d はそのまま（f_st を導入していない、v2s @ v2s' 方式）。
         MCons 非関数化はクリーンな新規ステップとしてではなく、
         既存の eval8a〜10c に直接パッチを当てる形（`8dcab48`/`c96672e`/`a80a6db`）で実施。
         実験枝 eval1e_1（trail 側も無理に非関数化しようとして頓挫、stash `12fe29b`）を持つ。
```

**重要**: `eval1-appterm-meta-optimize` は本ブランチとは前半（`eval1d` の有無、`f_st` の有無、
`Appterm` 相当命令の導入時期）から系統が異なる**別解**であり、そこでの成果を本ブランチへ
「merge」することはできない（当てにいくなら本ブランチの `f_st` ベースの後半に MCons 非関数化を
当て直す作業になる）。混同しないこと。

| | **本ブランチ (= main)** | **eval1-appterm-meta-optimize**（別解） |
|---|---|---|
| `eval1d` 周辺 | `1d_1`（補題適用）→`1d_2`（`f_st`導入）→`1d_3`（`app_s`展開）の3ステップ | 分岐前の `eval1d` のまま（`f_st` なし、`v2s @ v2s'`） |
| MCons 非関数化 | `1b_4` で独立ステップとして実施、以降の全フォルダに伝播済み | `eval8a`〜`eval10c` に直接パッチ（新規ステップ化していない） |
| Trail 非関数化 | `1b_5` で独立ステップとして実施 | 未実施（`eval1e_1` で試みて頓挫） |
| `Appterm` 相当命令 | `eval10c` で初めて導入 | `CAppS1T`(eval2a〜4c) → `IAppterm`(eval9a〜) と早くから存在 |

`jssst`（論文スナップショット）と `eval1-appterm` は本ブランチに完全包含される。
論文と突き合わせるときは `jssst` を見る。

### "st" パス（tail interpreter、最適化のお手本）

本ブランチ内に**すでにフォルダとして存在する**別系統（README の
「Tail interpreter revived (Journal ver.)」節）:

- `eval1s, eval1st, eval2st, eval5st (dummy VEmpty and s), eval5st1 (v2s を s に統合), eval7st, eval7st1, eval8st, eval9st, eval9st1, eval10st, eval10st1`
- メタ継続 `m` はすでに `MCons of (c * s * t) * m` — `(c, s, t)` という**裸の継続**を保存しており
  （`eval7st1/value.ml:18` 等で確認済み）、m-pop 時に `app_c` 相当のラッパーを**その場で遅延生成**する。
  **この "st" パスは "a" パスより先に最適化済みのお手本。**

**本ブランチの 1b_4/1b_5 以降の作業は、"st" パスですでに確立済みのこの最適化を "a" パスへ
移植する作業である。** "a" パスで迷ったら、同じ論文 step に対応する "st" パスのフォルダの
`eval.ml`/`value.ml` を読む（例: `eval8a` で迷ったら `eval8st` を見る）。

- "st" パス最適化の要点:
  - `m` に `(c, s, t)` を保存（裸の継続。`app_c` でラップしない）
  - m-pop 時に `app_c` 相当のラッパーを都度**遅延生成**する
    - クロージャベース（eval6a/8a 相当）: `fun (v :: s) t m -> app_s v c s t m`
    - CSeq ベース（eval9a/9b/9c 相当）: `CSeq(IReturn, [], c)`
    - 命令リストベース（eval10a/10b/10c 相当）: `([IReturn], []) :: c`

## 論文 step ↔ フォルダ 対応

`jssst` ブランチが論文（図 `fig:derivation-step-table`）に一致する。

| 論文 step | 内容 | 最適化 | 節 | jssst | 本ブランチ (= main) |
|---|---|---|---|---|---|
| 1a | definitional interpreter | | 5.2 | `eval1a` | `eval1a` |
| 1b | 末尾呼出用インタプリタの導出 | ✓ | 5.2 | `eval1b_{1,2,3}` | `eval1b_{1,2,3}` |
| （論文外） | `MCons` の非関数化 | ✓ | — | — | `eval1b_4` |
| （論文外） | `Trail` の非関数化 | ✓ | — | — | `eval1b_5` |
| 1c | `Grab` と `Apply` の原形の導出 | ✓ | 5.2 | `eval1c` | `1d_*` に吸収 |
| **1d** | **末尾の関数適用の最適化実装の挿入 ← 唯一の非自明ステップ** | ✓ | 5.2 | `eval1d` | `eval1d_{1,2,3}`（`f_st` 経由） |
| 2a | 継続の非関数化 | | 5.3 | `eval2a` | `eval2a` |
| 4a | 引数スタック導入 | | 5.3 | `eval4a` | 廃止 |
| 4b | 各関数クロージャの引数をスタックに積む | ✓ | 5.3 | `eval4b` | `eval4b` |
| 4c | 計算結果を引数スタックで渡す | | 5.3 | `eval4c` | `eval4c` |
| 6a | 継続の関数化 | | 5.4 | `eval6a` | `eval6a` |
| 8a | 継続のコンビネータ化 | | 5.4 | `eval8a` | `eval8a` |
| 9a | 継続の非関数化 | | 5.5 | `eval9a` | `eval9a` |
| 9b | 関数抽象とトレイルの非関数化 | | 5.5 | `eval9b` | `eval9c` に統合 |
| 10a | 継続を命令のリストとして実装 | | 5.5 | `eval10a` | `eval10a` |
| 10b | リターンスタック操作の最適化 | ✓ | 5.5 | `eval10b` | `eval10b` |
| （論文外） | `Appterm` 命令の導入（`Apply` の Return 最適化版） | | — | `eval10c` | `eval10c` |

論文の step 番号とフォルダ名はブランチによってズレる。**論文を引くときは step 番号、
コードを触るときはフォルダ名**で考え、対応はこの表で引く。
`eval1b_4`/`eval1b_5`（MCons・Trail 非関数化）は論文には存在しない、本ブランチ固有の
追加ステップであることに注意。

## ビルドとテスト

```bash
cd eval8a && make test    # test-suite/check-vm で 0〜4 を実行（36 tests、2026-09-12 時点）
```

- **`make test` は最後に `make clean` を走らせる**（Makefile の test ターゲット）
- 前提: `~/include/OCamlMakefile`（導入済み）、opam の ocaml
- `make` だけなら `./interpreter` が生成される。標準入力にコードを与え Control-D で実行

## ファイル構成（各 eval* フォルダ共通）

`syntax.ml` → `parser.mly` → `lexer.mll` → `env.ml` → `value.ml` → **`eval.ml`** → `main.ml`

導出で触るのは基本 `eval.ml` のみ。`value.ml` は継続や命令の型が変わるステップでのみ触る。
