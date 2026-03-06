The compiler driver `vcomp` is a version of `ccomp` that compiles the Cminor program statically defined in [./import/ImportProgram.v](./import/ImportProgram.v).

Synopsis:
```sh
make -j16
./vcomp -c	# ImportProgram.o
./vcomp ImportProgram.o -o a.out
```
