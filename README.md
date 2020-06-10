## An experimental LLVM backend for L3

This Rust crate implements a small parser for L3 CPS (low) trees (as output by the L3 reference compiler's pretty printer) and a code generator on those trees.
Internally, we use a Rust library called Inkwell that provides safe bindings to LLVM and allows us to directly emit and run these functions via LLVM's JIT compiler.

LLVM must be installed to run the backend. Various versions of LLVM should work, but will have to be configured in `Cargo.toml`. Furthermore, when compiling the crate, the path to LLVM should be provided in the appropriate environmental variable. For standard installations of LLVM (e.g., version 6.0) it should be possible to simply export the correct value using
```bash
export LLVM_SYS_60_PREFIX=$(llvm-config-6.0 --prefix)
```
As a sanity check, one can run `cargo test`, which will perform some basic tests for both parsing and code generation.

A binary called `l3jit` is included, which consumes L3 CPS programs and executes them.
For instance, take [bignums.l3cps](tests/bignums.l3cps), which reads an integer, computes its factorial, and writes the result back out.
You can try this for yourself by running `echo 5 | cargo run tests/bignums.l3cps`.
