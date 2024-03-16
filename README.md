# ochacaml4d-definitional-interpreter
Derive OchaCaml4D from definitional interpreter

## How to test

- Download [OcamlMakefile](https://github.com/mmottl/ocaml-makefile/blob/master/OCamlMakefile) into `~/include/OCamlMakefile`.
- Run the following to generate a binary named `interpreter`.

```shell
$ cd eval1/
$ make
```

- Run the test case to check the behavior.

```shell
$ ../test-suite/check-vm eval1/interpter 0
```