# Induced-matching packing in maximum-degree-four graphs: from 19.5 to 19

This repository proves the prescribed-edge bound

\[
|F|\le 19\nu_s^G(F)+t_G(F).
\]

**Status on 11 October 2026: the corrected 19 theorem is Lean-verified for every candidate set and every matching number.** The independent Route B extension proves the matching-witness statement, the independence-number statement, and the correction by actual original connected components. See [the main theorems](route-b/lean/StrongEdge19/Main.lean) and [the recorded build and axiom audit](route-b/verification/lean-extension/README.md).

All strong conflicts are evaluated in the complete original graph `G`. Original edges outside `F` remain available as conflict witnesses. The correction `t_G(F)` counts only original `C5[2]` components whose entire twenty-edge sets belong to `F`.

Read the [complete English proof aligned with the optimized Lean development](route-b/manuscript/packing19.md). It presents the structural lemmas, the candidate-degree-only Stage 2 interface, nineteen-clique completion, exact compensation, and component restoration, with a concordance covering all 83 extension declarations.

The [complete English PDF manuscript](route-b/manuscript/packing19.pdf) follows the companion 19.5 paper's format, including Congyue Mao's byline and a separate AI-assistance disclosure. [Publishing source and reproduction instructions](route-b/manuscript/README.md) accompany the PDF.

The optimized proof and its complete English manuscript are merged into the default branch, `codex/route-b-stage1`. The original verified 19 implementation remains available at tag `strongedge19-verified-original` (commit `cbc6f7b50f5defb2e03e9291dc3ccac2ff0e7abc`). Both implementations and their verification records remain in the repository history.

## Research routes

- [Independent audit report and reproducible evidence for commit 028f4d3](route-b/audit-2026-10-11/README.md)
- [Route B: global compensation and critical configurations](route-b/README.md)
- [Stage 1: the exact identity and critical normalization](route-b/notes/route-b-stage1.md)
- [Stage 2: a paper exclusion of all five 39-edge cases](route-b/notes/route-b-stage2.md)
- [Stage 3: critical-clique rigidity and the general paper proof](route-b/notes/route-b-stage3.md)
- [Stage 3 finite template checks](route-b/results/stage3-checks.json)
- [New Lean extension and exact formalization scope](route-b/lean/README.md)
- [New Lean verification and axiom audit](route-b/verification/lean-extension/README.md)
- [Stage 2 interface review and before/after measurements](route-b/notes/candidate-degree-interface-review.md)
- [Verification scope and reproduction](route-b/verification/README.md)
- [Recorded upstream verification results](route-b/verification/results.json)

All repository documentation, source comments, filenames, and new research records are maintained in English.

## Verified foundation

The corrected 19.5 theorem, five conflict-degree clique bounds, twenty-clique rigidity, and original-component correction come from [strong-edge-packing-195](https://github.com/congyuemao/strong-edge-packing-195).

The upstream Git submodule is fixed at commit `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`:

- [English manuscript](upstream/packing195/manuscript/packing195.md)
- [Lean main theorem](upstream/packing195/lean/StrongEdge/TightComponents.lean)
- [Existing local 39 bound](upstream/packing195/lean/StrongEdge/MinimalPacking195.lean)

The new extension and its verification records are separate from the existing Lean theorems and historical upstream build logs.

The checked proof excludes all five zero-deficit cases for a tertiary-optimal maximum independent set after removing fully selected exceptional components. It proves the stronger pointwise statement `delta(e) >= 1`, hence `sum delta + R >= |M|` for arbitrary matching number. Restoring each exceptional component adds one matching edge and one correction unit. The pinned 19.5 project remains unchanged.

The new proof uses original-graph degree and neighbour saturation, including unselected original witness edges. The finite checks concern explicitly stated templates and boundary examples; they are not an exhaustive search over original graphs or a substitute for formal verification.

## Initialize the pinned source

```sh
git submodule update --init --recursive
```

Do not use `git submodule update --remote` to replace the audited source revision. New research must preserve the verified mathematical source, toolchain, and dependency lockfiles.

Route-specific derivations, programs, and evidence belong in their respective route directories. The upstream source is shared across routes.
