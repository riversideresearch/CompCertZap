# External Integrations

**Analysis Date:** 2026-03-14

## APIs & External Services

**No external APIs or cloud services used.**

CompCert is a self-contained compiler. It does not integrate with:
- Cloud platforms (AWS, GCP, Azure)
- Third-party web services or APIs
- Remote code generation or analysis services
- Package repositories beyond OPAM (OCaml package manager)

## Data Storage

**Databases:**
- **Not used** - CompCert is a command-line batch compiler; no persistent data storage

**File Storage:**
- **Local filesystem only** - All I/O is to local disk
  - Input: C source files (`.c`), header files (`.h`)
  - Output: Assembly (`.s`), object files (`.o`), executables, debug dumps (`.rtl`, `.light.c`, `.json`)
  - Temporary files: Via `tmp_file` function in `driver/Driver.ml`

**Caching:**
- **No caching layer** - Compiler runs fresh for each invocation
- **Incremental builds:** Only via Make dependencies (`.vo`, `.cmi`, `.cmx` artifacts in build tree)

## Authentication & Identity

**Auth Provider:**
- **Not applicable** - No user authentication or identity management
- **No secrets or credentials** - No API keys, tokens, or authentication data required at runtime

## Monitoring & Observability

**Error Tracking:**
- **Not used** - No integration with error tracking services (Sentry, Rollbar, etc.)

**Logs:**
- **stderr/stdout only**
  - Error messages via `eprintf` to stderr (`Printf.eprintf`)
  - Compiler diagnostics to stdout
  - Optional debug output to files (`.parsed.c`, `.light.c`, `.rtl`, `.mach`, `.alloctrace`) via `Cprint.destination` and related refs
  - Configuration file errors logged to stderr with file/line info via `Configuration.ml`

**Timing/Profiling:**
- Optional Coq compilation timing via `-time-file` flag (Coq ≥8.18)
- Optional Coq profiling via `-profile` flag (Coq ≥8.19), output as `.prof.json` gzipped
- OCaml runtime profiling: Not integrated

## CI/CD & Deployment

**Hosting:**
- **Self-hosted** - CompCert is installed locally via `make install`
  - Installation paths configurable via `./configure -prefix`, `-bindir`, `-libdir`, etc.
  - Default: `/usr/local/bin/ccomp`, `/usr/local/lib/compcert/`

**CI Pipeline:**
- **Not detected** - No CI configuration (GitHub Actions, GitLab CI, Travis, CircleCI, etc.) in repo
- Manual build via `make -j$(nproc) all` (documented in `CLAUDE.md`)

## Environment Configuration

**Required env vars:**
- **None at runtime** - All configuration is static or command-line driven
- **Build-time env vars:**
  - `COQBIN` - Path to Coq installation (auto-detected, e.g., `/path/to/bin/`)
  - `MENHIR_DIR` - Path to MenhirLib (detected from OPAM, set in `Makefile.config`)
  - `ARCH`, `BITSIZE`, `SYSTEM` - Architecture specifics (set by `./configure`)

**Configuration file:**
- **compcert.ini** - Optional runtime configuration for target-specific options
  - Location: Searched in standard paths (compile-time specified `sharedir`)
  - Parsed by `driver/Configuration.ml` via `Readconfig.ml` (ocamllex-based lexer)
  - Purpose: Architecture-specific compiler flags, target feature bits (e.g., ISA extensions)
  - Error handling: Logs to stderr on parse failure, exits with code 2

**Secrets location:**
- **Not applicable** - No secrets management needed

## Webhooks & Callbacks

**Incoming:**
- **Not applicable** - CompCert is a batch compiler, not a service with webhooks

**Outgoing:**
- **Not applicable** - No outbound webhooks or callbacks to external systems

## Build-Time Dependencies (Non-Bundled)

**Requires OPAM package:**
- **menhirLib** (via `MENHIR_DIR=/home/alex/.opam/4.14.2/lib/menhirLib`)
  - Alternative: Bundled local copy in `MenhirLib/` if `LIBRARY_MENHIRLIB=local` (default)
  - External installation: `./configure -use-external-MenhirLib`

- **Coq** (proof checker and extraction engine)
  - Auto-detected at configure time via `coqc --print-version`
  - Supported versions: 8.15–9.1 (checked in configure, can override with `-ignore-coq-version`)

## Generated Code & Artifacts

**Coq Extraction:**
- **RTLinfercolor oracle** (`backend/RTLinfercolor.ml`)
  - Unverified OCaml color inference implementation
  - Integrated via `extraction/extraction.v`: `Extract Constant RTLcolorcheck.infer_coloring => "RTLinfercolor.infer_coloring"`
  - Responsible for computing well-colored register assignment (fault tolerance critical path)

**Parser Generation:**
- **cparser/Parser.ml(i)** - Generated from `cparser/Parser.vy` by Menhir
- **cparser/Lexer.ml(i)** - Generated from `cparser/Lexer.mll` by ocamllex
- **cparser/pre_parser_messages.ml** - Error message database (generated via `make -C cparser correct`)

## Runtime Libraries

**libcompcert.a** (`runtime/libcompcert.a`)
- Static library containing architecture-specific runtime support
- Contents: 64-bit integer operation stubs (e.g., `i64_dtou.o`, `i64_utod.o`, `vararg.o`)
- Built from: `runtime/{x86_64,arm,aarch64,powerpc,riscV}/*.S` (assembly) or `runtime/c/*.c` (C)
- Linked with compiled programs to provide CompCert-generated code with runtime helpers

**Standard Headers** (`runtime/include/`)
- Optional installation (`-no-standard-headers` to skip)
- Provided headers: `float.h`, `stdarg.h`, `stdbool.h`, `stddef.h`, `varargs.h`, `stdalign.h`, `stdnoreturn.h`

---

*Integration audit: 2026-03-14*
