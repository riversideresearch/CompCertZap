# Configure OCaml build

```bash
CC=ccomp ./configure --enable-imprecise-c99-float-ops --disable-systhreads --build=aarch64-pc-linux --enable-shared=no
```

Do steps in patch.py.

# Fix linux header files

Add to `/usr/lib/linux/uapi/arm64/asm/sigcontext.h`, above definition of `struct fpsimd_context`:
```c
typedef unsigned long long __uint128_t;
```

Add to `/usr/include/linux/types.h`, above `#ifdef __SIZEOF_INT128__`:
```c
#undef __SIZEOF_INT128__
```
