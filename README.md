# ochacaml4d-definitional-interpreter
Derive OchaCaml4D from definitional interpreter

## How to test

- Download [OcamlMakefile](https://github.com/mmottl/ocaml-makefile/blob/master/OCamlMakefile) into `~/include/OCamlMakefile`.
- Run the following to generate a binary named `interpreter`.

```shell
$ cd eval1/
$ make
```

- From the same directory, run the test cases.

```shell
$ ../test-suite/check-vm ./interpter 0
```