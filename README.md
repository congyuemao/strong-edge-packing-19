# Induced-matching packing in maximum-degree-four graphs: from 19.5 to 19

This repository studies the conjectured prescribed-edge bound

\[
|F|\le 19\nu_s^G(F)+t_G(F).
\]

**Status on 11 October 2026: the general 19 bound is unproved, and no counterexample has been found in this project.**

All strong conflicts are evaluated in the complete original graph `G`. Original edges outside `F` remain available as conflict witnesses. The correction `t_G(F)` counts only original `C5[2]` components whose entire twenty-edge sets belong to `F`.

## Research routes

- [Route B: global compensation and critical configurations](route-b/README.md)
- [Stage 1: the exact identity and critical normalization](route-b/notes/route-b-stage1.md)
- [Stage 2: a paper exclusion of all five 39-edge cases](route-b/notes/route-b-stage2.md)
- [Verification scope and reproduction](route-b/verification/README.md)
- [Recorded upstream verification results](route-b/verification/results.json)

All repository documentation, source comments, filenames, and new research records are maintained in English.

## Verified foundation

The corrected 19.5 theorem, five conflict-degree clique bounds, twenty-clique rigidity, and original-component correction come from [strong-edge-packing-195](https://github.com/congyuemao/strong-edge-packing-195).

The upstream Git submodule is fixed at commit `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`:

- [English manuscript](upstream/packing195/manuscript/packing195.md)
- [Lean main theorem](upstream/packing195/lean/StrongEdge/TightComponents.lean)
- [Existing local 39 bound](upstream/packing195/lean/StrongEdge/MinimalPacking195.lean)

New paper arguments are identified separately from existing Lean theorems. Upstream build logs do not certify the new arguments.

Stage 2 now contains a **paper proof, not yet formalized**, of the corrected 19 bound when the induced-matching number is at most two. For matching number three, it excludes the 58-edge case with `R=1` and records the remaining `R=0` configuration. The general conjecture remains unproved.

## Initialize the pinned source

```sh
git submodule update --init --recursive
```

Do not use `git submodule update --remote` to replace the audited source revision. New research must preserve the verified mathematical source, toolchain, and dependency lockfiles.

Route-specific derivations, programs, and evidence belong in their respective route directories. The upstream source is shared across routes.
