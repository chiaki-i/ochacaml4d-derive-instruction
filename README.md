# ochacaml4d-derive-instruction

> [!WARNING]
> This is a development repository containing code under verification.
> The complete artifact is published at https://github.com/chiaki-i/ochacaml4d-instruction.

This repository contains implementations of Delimited continuation operators' Abstract Machine (DAM).
DAM extends the ZINC Abstract Machine instruction set with four delimited continuation operators.
The step-by-step derivation process is organized in each `eval*` folder.

## How to run the code

- Save [OcamlMakefile](https://github.com/mmottl/ocaml-makefile/blob/master/OCamlMakefile) as `~/include/OCamlMakefile`, or modify `OCAMLMAKEFILE` value in each `eval*/Makefile` to the desired local path.
- Under `eval*` directory, run `make test` to compile and test the interpreter. After every test, all executables are cleaned up.

## Which directory is for which derivation path?

### Tail version revived (2025 Feb)
- At first, Eval1st included f1st to handle multi-arg tail call, but it was integrated with f1s.
- Eval1st, 2st, 5st, 5st1 (integrate v2s into s), 7st, 7st1, 8st, 9st, 9st1, 10st
- Eval1st1, 5st2 is experimental

### part of c represents return stack (Jan 19-25)
- Eval1s, 2s, 4s, 5s, 5s2, 7ds, 7ds1, 7ds4 (w/o CSeq), 8s, 9s2, eval10s

### With return stack, better env management (after PPL)
- Eval1s, 2s, 5sr, 7ds3v, 7ds4v, 8sv, 9sv, 10sv, 10sv2, 10sv3, 10sv4, 10sv5, 11sv

### Functions with multiple arguments (PPL)
- Eval1s, 2s, 5ds2, 7ds1, 7ds3, 7ds4, 8ds, 9ds
