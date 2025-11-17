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

## Which directory is for which derivation path?

### Appterm (Journal revision)
- Eval1a, 1b_{1,2,3}, 1b_3_2, 1c, 2a, 4{a,b,c}, 6a, 8a, 9{a,b,c}, 10a
  - 1b_3_1 は、Appterm 導出しようとして f と f_t の App 規則を非関数化しようとしている（が、うまく行っていない）
  - 1b_3_2 は Appterm はこうあるべき、という形を意図的に定義している。App のケースで、app_s ではなくて app を使用している点にも注意

### Tail interpreter revived (Journal ver.)
- Eval1s, Eval1st, 2st, 5st (dummy VEmpty and s), 5st1 (integrate v2s into s), 7st, 7st1, 8st, 9st, 9st1, 10st, 10st1
  - Eval1st1, 5st2 is experimental

### part of c represents return stack (Jan 19-25)
- Eval1s, 2s, 4s, 5s, 5s2, 7ds, 7ds1, 7ds4 (w/o CSeq), 8s, 9s2, eval10s

### With return stack, better env management (after PPL)
- Eval1s, 2s, 5sr, 7ds3v, 7ds4v, 8sv, 9sv, 10sv, 10sv2, 10sv3, 10sv4, 10sv5, 11sv

### Functions with multiple arguments (PPL)
- Eval1s, 2s, 5ds2, 7ds1, 7ds3, 7ds4, 8ds, 9ds
