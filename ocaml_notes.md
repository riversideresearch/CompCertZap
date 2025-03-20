## Install 32-bit headers and libraries
```bash
sudo apt-get install gcc-multilib
```

## Install 32-bit CompCert

Using OCaml 4.14.2 with menhir (via opam):
```bash
./configure x86_32-linux
make all
sudo make install
```

## Install 32-bit OCaml (bytecode only) without CompCert
```bash
opam switch create 4.14.2+32bit ocaml-variants.4.14.2+options ocaml-option-bytecode-only ocaml-option-32bit
```

### Regular bytecode only (choose `<tag>` to be whatever)
```bash
opam switch create 4.14.2+<tag> ocaml-variants.4.14.2+options ocaml-option-bytecode-only
```

## Build OCaml 4.14.2 with CompCert

### Configure
```bash
./configure CC=ccomp --enable-imprecise-c99-float-ops --build=x86_64-pc-linux --host=i686-linux --enable-shared=no

./configure --build=x86_64-pc-linux --host=i386-linux CC=ccomp AS='as --32' ASPP='ccomp -c' PARTIALLD='ld -r -melf_i386' --disable-ocamldoc --enable-imprecise-c99-float-ops

```

### Patch makefile

```bash
python patch.py
```

### Modify changes

In `runtime/caml/misc.h`, replace the code for `caml_uadd_overflow`, `caml_usub_overflow`, and `caml_umul_overflow` with the following definitions:

```c
Caml_inline int caml_uadd_overflow(uintnat a, uintnat b, uintnat * res)
{
  uintnat c = a + b;
  *res = c;
  return c < a;
}

Caml_inline int caml_usub_overflow(uintnat a, uintnat b, uintnat * res)
{
  uintnat c = a - b;
  *res = c;
  return a < b;
}

extern int caml_umul_overflow(uintnat a, uintnat b, uintnat * res);
```

and replace
```c
#define CAMLalign(n) __attribute__((aligned(n)))
```
with
```c
#define CAMLalign(n) __attribute((aligned(n)))
```

and in `runtime/misc.c`, remove the `#if` block around
```c
CAMLexport int caml_umul_overflow(uintnat a, uintnat b, uintnat * res)
```

### Compile an OCaml program to bytecode

```bash
boot/ocamlrun boot/ocamlc -I boot -without-runtime <path/to/program.ml> -o <program_name>
```

### Run the program
```bash
boot/ocamlrun <program_name>
```