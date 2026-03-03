# External Integrations

**Analysis Date:** 2026-03-03

## APIs & External Services

**None detected** - CompCert is a self-contained compiler with no external API dependencies or web service integrations.

## Data Storage

**Databases:**
- **None** - This is a compiler, not a database application. No persistent storage of compilation state.

**File Storage:**
- **Local filesystem only**
  - Configuration read from `compcert.ini` (generated at build time)
  - Source C files provided as command-line arguments
  - Compiled object files (`.o`) and executables written to filesystem
  - Temporary files created in system temp directory via `Filename.temp_file` (in `driver/Driveraux.ml`)
  - Output controlled via `-o` flag to `ccomp`

**Caching:**
- **None** - No persistent caching. Compilation is stateless; each invocation is independent.
- Build artifacts (`.vo`, `.ml`, `.cmx` files) cached during build process via `Makefile` dependency tracking

## Authentication & Identity

**Auth Provider:**
- **None** - Compiler requires no authentication or identity management
- Configuration files (`compcert.ini`) read without credentials
- GCC toolchain invoked via system `PATH` (no special auth)

## Monitoring & Observability

**Error Tracking:**
- **None** - No external error tracking service
- Errors reported to stderr via OCaml `Printf` and `Diagnostics` module in `driver/`

**Logs:**
- **Console output** (stderr, stdout)
  - Compilation progress: `"COQC $*.v"`, `"OCAMLOPT"`, etc. (via Makefile echo)
  - Errors and warnings printed by driver (`driver/Driver.ml`)
  - Color checking results: `"RTL program is well-colored :)"` / `"RTL program not well-colored!"` (line 63-69 in `driver/Driver.ml`)
- **Optional dump files** (when requested via command-line flags):
  - `-dparse` → `.parsed.c` (parsed AST)
  - `-drtl` → `.rtl` (RTL intermediate form)
  - `-dclight` → `.light.c` (Clight intermediate form)
  - `-sdump` → `.json` (assembly as JSON)
  - `-dalloctrace` → `.alloctrace` (register allocation trace)

## CI/CD & Deployment

**Hosting:**
- **Build-time only** - CompCert is a compiler, not a hosted service
- Deployment is installation of compiled binaries: `make install` (installs `ccomp`, `clightgen`, `vcomp` to `$(BINDIR)`)

**CI Pipeline:**
- **None detected** - No GitHub Actions, Jenkins, Travis CI, or equivalent
- Build verified locally via `make proof` → `make extraction` → `make ccomp`
- Proof integrity check: `make check-proof` (runs `coqchk` on final module)
- Proof completeness check: `make check-admitted` (grep for `Admitted` proofs)

## Environment Configuration

**Required env vars:**
- **COQBIN** (optional) - Path to Coq binaries; defaults to system PATH
- **COMPCERT_CONFIG** (optional) - Path to `compcert.ini`; searched in standard locations if not set
- **OPAM environment** - OCaml-related vars when building (OCAMLPATH, etc.)

**Secrets location:**
- **No secrets** - Compiler contains no API keys, tokens, or credentials
- Configuration (`compcert.ini`, `Makefile.config`) is non-sensitive, build-time generated

## Webhooks & Callbacks

**Incoming:**
- **None** - Not applicable to a compiler

**Outgoing:**
- **None** - Compiler produces compiled code files, no external callbacks

## Execution Model

**Command-line interface:**
- `./ccomp [options] <input.c> -o <output>`
  - `-tmr` - Compile with Triple Modular Redundancy (fault tolerance extension)
  - `-dmr` - Compile with Dual Modular Redundancy
  - `-c` - Compile to object file only (no linking)
  - `-S` - Compile to assembly only (no object file)
  - `-E` - Preprocess only
  - Diagnostic flags: `-drtl`, `-dalloctrace`, `-sdump` (write intermediate forms)

**Process model:**
- Single-process, single-threaded execution
- Invokes external tools via system calls:
  - GCC for preprocessing, assembly, linking
  - Coq/OCaml tools during build (not at runtime)

## Compilation Pipeline

**External tool invocations at compile-time:**
```bash
gcc -m64 -U__GNUC__ -U__SIZEOF_INT128__ -E  # Preprocessor
gcc -m64 -c                                   # Assembler
gcc -m64                                      # Linker
```

**Generated tool invocations at build-time:**
```bash
coqc                                          # Coq proof verification
menhir                                        # C parser generation
ocamlc/ocamlopt                              # OCaml compilation
```

---

*Integration audit: 2026-03-03*
