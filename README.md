# ochacaml4d-derive-instruction

> [!WARNING]
> This is a development repository containing code under verification.
> The complete artifact is published at https://github.com/chiaki-i/ochacaml4d-instruction.

This repository contains implementations of Delimited continuation operators' Abstract Machine (DAM).
DAM extends the ZINC Abstract Machine instruction set with four delimited continuation operators.

## Structure of this repository
The repository contains multiple implementation versions that follow different derivation paths.
Each implementation represents a specific stage in the development of DAM.
The folders are organized chronologically and by feature implementation, allowing you to trace the evolution of the abstract machine design.

## Installation and usage

### Prerequisites

- Save [OcamlMakefile](https://github.com/mmottl/ocaml-makefile/blob/master/OCamlMakefile) as `~/include/OCamlMakefile`
  - If you want to save OcamlMakefile in a different location, modify the `OCAMLMAKEFILE` value in each `step*/Makefile` to the desired local path.

### Running the interpreter

- Navigate to the implementation folder you want to run (e.g., `step1a`).
```bash
$ cd step1a
```
- Compile the code, which will create an executable file named `./interpreter` in the same folder.
```bash
$ make
```
- Launch the interpreter and input the code you want to execute, then press Control-D at the end of your input, to run the code.
  - The supported syntax includes:
    - Integers and their basic arithmetic operations (`+`, `-`, `*`, `/`)
    - Function abstraction (`fun x -> ...`; the same as the anonymous functions in OCaml)
    - Function application
    - Delimited continuation operators (`shift k -> ...`, `control k -> ...`, `shift0 k -> ...`, `control0 k -> ...`, `reset ...`)
```bash
$ ./interpreter
(fun f -> (fun z -> f (z + 4)) 2 3) (fun x -> fun y -> x * y) # press Control-D at the end of your input
Parsed : ((fun f -> ((fun z -> (f (z + 4))) 2 3)) (fun x -> (fun y -> (x * y))))
Result : 18
$ ./interpreter
reset (2 * reset (1 + (shift h -> (shift f -> h (f 3))))) # press Control-D at the end of your input
Parsed : reset ((2 * reset ((1 + (shift h -> (shift f -> (h (f 3))))))))
Result : 8
```
- To remove the interpreter executables:
```bash
$ make clean
```

### Running the automated test suite for the interpreter

The `test-suite` folder contains code for testing the behavior of this interpreter.
- To run all test cases at once, navigate to the folder you want to test (e.g., `step1a`) and execute the `make test` command.
  - This will run all the prepared test cases and output their logs.
```bash
$ cd step1a
$ make test
Passed: /.../ochacaml4d-derive-instruction/test-suite/0/appterm.ml
Passed: /.../ochacaml4d-derive-instruction/test-suite/0/nested-app.ml
...
Passed: /.../ochacaml4d-derive-instruction/test-suite/4/test4.ml
34 test(s) passed
0 test(s) failed
```

## Derivation path

### Appterm (after JSSST Journal, `f_st` version)
- Eval1a, 1b_{1,2,3}, 1d_{1,2,3}, 2a, 4{b,c}, 6a, 8a, 9{a,c}, 10{a,b,c}
  - 1d_1 は eval1a の補題を忠実に適用しただけ（ZINC の `Appterm` の本質的なアイデア）
  - 1d_2 は、 `v2s @ v2s'` のように2つの引数列をリスト結合する（`v2s` と `v2s'` の間に pushmark を入れたあとに 取り除く）ことと、そもそも最初から pushmark を入れないことは同じと考え、`f_st` を導入する。
    - これの正当性の説明は残課題。
  - 1d_3 は、`app_s` を使っていたところを展開して `app` を使用する（後の `Apply` 命令の原形）
  - 最終的に、`Appterm` 命令は、`Apply` 命令の Return 最適化版として、eval10c で初めて導入される。

### Appterm (after JSSST Journal)
- Eval1a, 1b_{1,2,3}, 1d, 2a, 4{b,c}, 6a, 8a, 9{a,c}, 10{a,b,c}
  - eval1b_3_2（f_st による別経路）・eval1c はともに廃止。eval1b_3 → eval1d を1ステップとして扱う。
  - eval1b_3 -> eval1d の変換内容：
    - (1) f_t App ケース：補題（eval1a に証明あり）を `app_s v0 v2s (fun v t m -> app_s v v2s' c t m)` に直接適用し `app_s v0 (v2s @ v2s') c` を導出している。
    - (2) Grab のケース：`app_c VFun ...` を展開した形を導出
  - eval1d の `v2s @ v2s'` の形が eval2a 以降の `IAppterm` 命令の導出に直結する。
  - eval4a （空の引数スタックを引き回す）を廃止、eval2a から eval4b （引数スタックに、関数適用の引数を積む）を直接導出する。
  - eval4c は、引数スタックの先頭に引数を載せる。引数スタックが `v list list` 型であるため、単純な `::` 操作だとコードが長くなってしまうので便宜上 push という補助関数を導入。
  - eval6a2 は、eval4c で引数スタックの先頭に引数を載せるのではなく、`run_c` 等が引き回している値 `v` を accumulator として捉えようとしたもの。ただし、accumulator を導入するには、四則演算や複数引数の関数適用の際に acc から arg stack へ引数を push する必要がある点に注意（で、結局 push する操作を定義するならほとんど eval4c と変わらないか、と思い、戻ってきた）
  - eval9b と eval9c は統合して eval9c に。実は Journal でも実質的にはまとめて説明されていた。

### Appterm (Journal revision)
- Eval1a, 1b_{1,2,3}, 1b_3_2, 1c, 2a, 4{a,b,c}, 6a, 8a, 9{a,b,c}, 10{a,b,c}
  - 1b_3_1 は、Appterm 導出しようとして f と f_t の App 規則を非関数化しようとしている（が、うまく行っていない）
  - 1b_3_2 は Appterm はこうあるべき、という形を意図的に定義している。App のケースで、app_s ではなくて app を使用している点にも注意
  - 6a が非関数化する前の最後の状態、10c が return 最適化後の状態

### Tail interpreter revived (Journal ver.)
- Eval1s, Eval1st, 2st, 5st (dummy VEmpty and s), 5st1 (integrate v2s into s), 7st, 7st1, 8st, 9st, 9st1, 10st, 10st1
  - Eval1st1, 5st2 is experimental

### part of c represents return stack (Jan 19-25)
- Eval1s, 2s, 4s, 5s, 5s2, 7ds, 7ds1, 7ds4 (w/o CSeq), 8s, 9s2, eval10s

### With return stack, better env management (after PPL)
- Eval1s, 2s, 5sr, 7ds3v, 7ds4v, 8sv, 9sv, 10sv, 10sv2, 10sv3, 10sv4, 10sv5, 11sv

### Functions with multiple arguments (PPL)
- Eval1s, 2s, 5ds2, 7ds1, 7ds3, 7ds4, 8ds, 9ds
