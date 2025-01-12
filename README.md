# ochacaml4d-derive-instruction

Derive OchaCaml4D virtual machine instructions from the  definitional interpreter

## How to run

- Save [OcamlMakefile](https://github.com/mmottl/ocaml-makefile/blob/master/OCamlMakefile) as `~/include/OCamlMakefile`, or modify `OCAMLMAKEFILE` value in each `eval*/Makefile` to the desired local path.
- Under `eval*` directory, run `make test` to compile and test the interpreter. After every test, all executables are cleaned up.

## Which directory is for which derivation path?

Below is all the trials so far.

### With return stack (most recent)
- Eval1s, 2s, 5sr, 7ds3v, 7ds4v, 8sv, 9sv, 10sv, 10sv2, 10sv3, 10sv4

### Functions with multiple arguments (PPL)
- Eval1s, 2s, 5ds2, 7ds1, 7ds3, 7ds4, 8ds, 9ds