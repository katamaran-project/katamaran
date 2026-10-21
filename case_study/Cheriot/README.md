# CHERIoT case study

The Makefile translates the CHERIoT Sail model to Microsail with `make sail` (`make test` translates only `prelude.sail`, `make csim` builds the C simulator).
`CHERIOT_SAIL_DIR` is required and must point to a cheriot-sail checkout.
`SAIL` defaults to the installed `sail`; to test a sail-backend branch without installing it, run `dune build` in its worktree and set `SAIL` to that worktree's `bin/sail-local`.
`OUT_DIR` (default: this directory) is where the generated `.v` files, `sail_smt_cache` and `z3_problems` go; give each run its own so parallel runs don't clash.
Use absolute paths for `OUT_DIR` when make is started from a script rather than a shell (see the Makefile).

```sh
cd /path/to/my-sail-backend-worktree
dune build
make -C /path/to/katamaran/case_study/Cheriot sail \
    CHERIOT_SAIL_DIR=/path/to/cheriot-sail \
    SAIL=/path/to/my-sail-backend-worktree/bin/sail-local \
    OUT_DIR=/path/to/cheriot-out
```
