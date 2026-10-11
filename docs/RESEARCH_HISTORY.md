# Research history and archive index

[Repository overview](../README.md) · [Current proof guide](PROOF_GUIDE.md) · [Verification](VERIFICATION.md)

This chronological index points to preserved records. The [consolidated manuscript](../route-b/manuscript/packing19.md) and [current Lean endpoint](../route-b/lean/StrongEdge19/Main.lean) present the final argument. Earlier notes retain their original scope, including approaches superseded by the general proof. Links to commits identify recorded milestones; links to local files open their preserved publication versions, which may contain later status annotations.

The Route B milestones below are dated **11 October 2026 in Australia/Sydney**, as recorded in Git. Commit links are authoritative for the state at each milestone.

## Corrected 19.5 foundation

**Role: final proof dependency and prior verification evidence.** The foundation is fixed at [`2e91b05b25a4ee931a0490fefcdbb4f253be95c8`](https://github.com/congyuemao/strong-edge-packing-195/commit/2e91b05b25a4ee931a0490fefcdbb4f253be95c8). Its [paper](../upstream/packing195/manuscript/packing195.md), [local-39 estimate](../upstream/packing195/lean/StrongEdge/MinimalPacking195.lean), and [component-count endpoint](../upstream/packing195/lean/StrongEdge/TightComponents.lean) provide the earlier results. The [Stage 1 upstream verification](../route-b/verification/README.md) preserves build and axiom evidence for this dependency, not a verification of the later nineteen proof.

## Stage 1: counting and normalisation

**Role: historical derivation of final proof ingredients; upstream verification evidence.** Commit [`b07f521`](https://github.com/congyuemao/strong-edge-packing-19/commit/b07f521333c1822e0cf330255c17875e1f09302f) records the exact identity audit and critical normalisation. The [Stage 1 note](../route-b/notes/route-b-stage1.md) develops compensation and the critical configurations. Its counting ideas persist in [Compensation.lean](../route-b/lean/StrongEdge19/Compensation.lean); its historical verification did not yet formalise the completed nineteen bound or perform a general 39-edge search.

## Stage 2: the 39-edge investigations

**Role: historical paper investigations and finite experiments.** Commit [`8c9287c`](https://github.com/congyuemao/strong-edge-packing-19/commit/8c9287ca20917bb44c9a85f2dc0249ffb9af5120) records the English-only organisation and paper exclusion of the matching-number-two obstruction. The [Stage 2 note](../route-b/notes/route-b-stage2.md), [checker](../route-b/scripts/check_stage2.py), and [results](../route-b/results/stage2-checks.json) retain the degree-case analysis, 72 labelled templates, and four exact boundary examples.

The finite enumeration covers its stated families. It is not an exhaustive 39-edge original-graph search. The later universal proof does not depend on the separate small-matching-number exchange route; its Stage 2 interface derives candidate degree nineteen using general structural lemmas.

## Stage 3: rigidity and the general argument

**Role: historical paper proof, final structural ingredient, and finite experiments.** Commit [`267e2c2`](https://github.com/congyuemao/strong-edge-packing-19/commit/267e2c2052b8cad8c1cfe77d66eaa72c49d0be44) records the paper compensation argument through nineteen-clique rigidity. See the [Stage 3 note](../route-b/notes/route-b-stage3.md), [finite checker](../route-b/scripts/check_stage3.py), and [results](../route-b/results/stage3-checks.json).

Commit [`b744794`](https://github.com/congyuemao/strong-edge-packing-19/commit/b7447943da89680d07925e2c2ab805ecbf10d8f0) adds formal compensation and nineteen-clique rigidity. The [formalisation progress record](../route-b/notes/lean-formalization-progress.md) explains the adaptations. The current original-graph extension is in [NineteenRigidity.lean](../route-b/lean/StrongEdge19/NineteenRigidity.lean); this milestone alone should not be confused with the later completed packing endpoint.

## First completed nineteen proof

**Role: completed formal proof and retained verification evidence.** Commit [`cbc6f7b`](https://github.com/congyuemao/strong-edge-packing-19/commit/cbc6f7b50f5defb2e03e9291dc3ccac2ff0e7abc), also identified by tag `strongedge19-verified-original`, completes the corrected bound for every candidate set and matching number. Its [archived baseline results](../route-b/verification/interface-refactor/baseline/results.json) and [raw compilation/axiom log](../route-b/verification/interface-refactor/baseline/build-and-audit.log) preserve the earlier implementation's verification.

## Optimised interface and consolidated manuscript

**Role: current proof interface, comparison evidence, and documentation.** Commit [`2c20ac6`](https://github.com/congyuemao/strong-edge-packing-19/commit/2c20ac6099a0fb581367e3bee39465aafec5f879) refactors Stage 2 around candidate degree nineteen. The [interface review](../route-b/notes/candidate-degree-interface-review.md) and [before/after evidence](../route-b/verification/interface-refactor/README.md) explain the retained tertiary normalisation inside high-degree cases and the later recovery of neighbourhood closure. The measurements are individual recorded runs, not a statistically established performance claim.

Commit [`6028859`](https://github.com/congyuemao/strong-edge-packing-19/commit/60288594461d26b66d74ef17c503a91416666e02) adds the [complete English manuscript](../route-b/manuscript/packing19.md) and its declaration concordance. Merge [`028f4d3`](https://github.com/congyuemao/strong-edge-packing-19/commit/028f4d3541ad41a558b3d1f5c8fd962046ea24dd) combines that manuscript with the optimised proof and is the snapshot examined by the independent audit. The [extension verification record](../route-b/verification/lean-extension/README.md) and [candidate archive](../route-b/verification/interface-refactor/candidate/results.json) describe the optimised source, while the baseline archive retains the original version.

## PDF and independent audit publication

**Role: documentation and publishing evidence.** Commit [`cb9ac30`](https://github.com/congyuemao/strong-edge-packing-19/commit/cb9ac302a388d10e7c742e58b90ba4c5294a170d) adds the [complete PDF](../route-b/manuscript/packing19.pdf) and its [publishing provenance](../route-b/manuscript/README.md). This publication occurred after the mathematical snapshot chosen for audit.

**Role: snapshot-specific verification evidence.** Commit [`b6e81c2fad48c681e8922cf9768c42f40d94f910`](https://github.com/congyuemao/strong-edge-packing-19/commit/b6e81c2fad48c681e8922cf9768c42f40d94f910) publishes the [independent audit report](../route-b/audit-2026-10-11/REPORT.md), [summary](../route-b/audit-2026-10-11/audit-summary.json), and [reproduction bundle](../route-b/audit-2026-10-11/README.md). These assess `028f4d3541ad41a558b3d1f5c8fd962046ea24dd`, not the later PDF or this navigation layer. Publication of an audit bundle is not journal publication or external human peer review.

All existing notes, scripts, results, raw logs, and snapshot guidance remain at their original repository paths. This index supplies navigation; it does not replace those records or promote every historical observation to a separately formalised theorem.
