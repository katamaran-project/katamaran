# Patches

This directory contains patches for the case studies.
All patches should be **applied from the root directory of this project**.
We provide a `make` command to apply an example patch: `make patch`, the patch can then be reverted with `make unpatch` (these commands need to be run from the root directy).
We currently provide the following patches:

| Case Study  | Patch File                        | Description                                           |
|-------------|-----------------------------------|-------------------------------------------------------|
| MinimalCaps | `MinimalCaps/duplicate_add.patch` | Adds a duplicate instruction for `add`, called `add'` |
| RiscvPmp    | `RiscvPmp/duplicate_add.patch`    | Adds a duplicate instruction for `add`, called `add'` |

