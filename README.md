# Induced-matching packing in maximum-degree-four graphs: from 19.5 to 19

This repository studies the conjectured prescribed-edge bound

\[
|F|\le 19\nu_s^G(F)+t_G(F).
\]

**Status on 11 October 2026: Route B contains a complete paper proof and a partially completed Lean formalization.** The new Lean extension verifies the compensation identity, tertiary normalization, nineteen-clique rigidity, and exclusion of critical degree nineteen. The new Stage 2 exclusions for degrees twenty through twenty-three and the full corrected 19 theorem remain to be formalized. The complete Lean-certified packing bound remains 19.5.

All strong conflicts are evaluated in the complete original graph `G`. Original edges outside `F` remain available as conflict witnesses. The correction `t_G(F)` counts only original `C5[2]` components whose entire twenty-edge sets belong to `F`.

## Research routes

- [Route B: global compensation and critical configurations](route-b/README.md)
- [Stage 1: the exact identity and critical normalization](route-b/notes/route-b-stage1.md)
- [Stage 2: a paper exclusion of all five 39-edge cases](route-b/notes/route-b-stage2.md)
- [Stage 3: critical-clique rigidity and the general paper proof](route-b/notes/route-b-stage3.md)
- [Stage 3 finite template checks](route-b/results/stage3-checks.json)
- [New Lean extension and exact formalization scope](route-b/lean/README.md)
- [New Lean verification and axiom audit](route-b/verification/lean-extension/README.md)
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

On paper, Stage 2 reduces every zero-deficit centre to a private nineteen-clique whose members have full conflict degree at least nineteen. Stage 3 proves that such a clique lies in an original `C5[2]` component; that rigidity statement is now also checked in the new Lean extension. The paper chain then excludes all zero-deficit centres after component removal and yields `sum delta + R >= |M|` for arbitrary matching number. Its Stage 2 reduction is still pending formalization.

The new proof uses original-graph degree and neighbour saturation, including unselected original witness edges. The finite checks concern explicitly stated templates and boundary examples; they are not an exhaustive search over original graphs or a substitute for formal verification.

## Initialize the pinned source

```sh
git submodule update --init --recursive
```

Do not use `git submodule update --remote` to replace the audited source revision. New research must preserve the verified mathematical source, toolchain, and dependency lockfiles.

Route-specific derivations, programs, and evidence belong in their respective route directories. The upstream source is shared across routes.
