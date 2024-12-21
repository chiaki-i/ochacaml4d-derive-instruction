# ochacaml4d-derive-instruction

Derive OchaCaml4D virtual machine instructions from the  definitional interpreter

## How to run

- Save [OcamlMakefile](https://github.com/mmottl/ocaml-makefile/blob/master/OCamlMakefile) as `~/include/OCamlMakefile`, or modify `OCAMLMAKEFILE` value in each `eval*/Makefile` to the desired local path.
- Compile to make `eval*/interpreter`.

```shell
$ cd eval1/
$ make
```

- From the same directory, run the test cases.

```shell
$ ../test-suite/check-vm ./interpter 0
```