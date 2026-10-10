# Independent audit of the corrected nineteen-packing project

Audit date: 11 October 2026 (Australia/Sydney).

Repository: <https://github.com/congyuemao/strong-edge-packing-19>.

Audited commit: `028f4d3541ad41a558b3d1f5c8fd962046ea24dd`.
Pinned foundation: `upstream/packing195` at `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`.
The manuscript identifies mathematical source commit `2c20ac6099a0fb581367e3bee39465aafec5f879`; its source hashes were checked against the preserved verification record.

## Assessment

No substantiated proof error, circular argument, concealed structural hypothesis, or mismatch invalidating the main theorem was found in this snapshot. The result being audited is precisely

\[
 |F|\leq 19\nu_s^G(F)+t_G(F)
\]

for every finite simple graph of maximum degree at most four and every prescribed original edge set. The correction counts actual original connected components isomorphic to the doubled five-cycle whose entire edge sets are selected.

This assessment combines mathematical review, definition and interface inspection, independent source compilation, elaborated dependency inspection, and reproduction of finite checks. It does not treat successful compilation alone as evidence that the definitions express the intended theorem, and does not treat finite examples as a universal proof.

All **104/104 project modules** compiled successfully from source. The independent environment inspection passed for **1,521 project-origin declarations**, including private/generated declarations; **327** originate in the extension. Every inspected project theorem body was available. The transitive axiom union is exactly **`propext`, `Classical.choice`, `Quot.sound`**, with no project axiom or unsafe declaration. The explicit endpoint-matching wrapper also compiled successfully with only these axioms.

## Scope and evidence

The audited project contains 104 Lean files and 13,392 lines across the extension and pinned foundation. Of these, 29 files belong to the extension; 27 contain the 83 mathematical declarations mapped in the manuscript. Audit and umbrella modules account for the other two extension files.

The review covered the consolidated manuscript, historical Stage 1–3 arguments and their disclosed scope, the extension's definitions and proof chain, the foundational graph/conflict/component definitions, and the upstream structural interfaces on which the extension depends. Every project Lean module is included in the source compilation, including upstream audit/test modules. The library dependencies are treated separately below.

| Evidence | What it establishes |
| --- | --- |
| [Machine-readable audit summary](audit-summary.json) | Final statuses, pinned commits, verification counts and repository-integrity checks. |
| [Source scan](source-scan.json) | All 104 source files scanned for placeholders, custom axioms, unsafe/native escapes, custom elaboration and opaque declarations; no flagged tokens. |
| [Clean source build](clean-build-results.json), [compiler log](clean-build.log) | Per-module compiler results, source hashes, output hashes, dependency order and exact library search path. |
| [Environment inspection](environment-audit.json), [raw output](environment-audit.log) | Elaborated types, transitive axioms, project declarations including generated/private declarations by originating module, and selected dependency closures. |
| [Toolchain provenance](toolchain-provenance.json) | Official archive digest and installed executable/library comparison. |
| [Manuscript provenance](manuscript-provenance.json) | Source correspondence, 83-declaration concordance, links and documentary checks. This is not a proof checker for English prose. |
| [Finite regression results](finite-regressions.json) | Independent rerun of the stated finite families, reproducing stored results. |

## Hidden axioms and assumptions

The lexical scan found no `sorry`, `admit`, `sorryAx`, custom `axiom`, `unsafe`, `native_decide`, `ofReduceBool`, `implemented_by`, `extern`, custom `opaque`, or custom elaborator declaration in either project's Lean source. The only explicit options found were `maxHeartbeats 400000` and `synthInstance.maxSize 1000`, which raise resource limits rather than weaken proof checking.

The environment inspector checks declarations according to their **originating project module**, rather than only their public names. This includes generated/private declarations and avoids relying exclusively on the repository's manually listed `#print axioms` commands. It rejects project axioms, unsafe declarations and any transitive axiom outside the standard set `propext`, `Classical.choice`, `Quot.sound`.

These three names must not be described as "no axioms": they are the usual propositional extensionality, classical choice and quotient soundness assumptions of the Lean/mathlib foundation. They are not graph-theoretic assumptions or assumptions of the desired nineteen bound. The report distinguishes their presence from adding a new mathematical axiom or `sorryAx`.

The principal theorem is [Main.lean](../lean/StrongEdge19/Main.lean), `prescribed_edge_bound19`. Its only structural graph hypothesis is `hDelta : forall x, G.degree x <= 4`. The finite vertex type and the usual decidability instances do not impose connectivity, triangle-freeness, bipartiteness, absence of exceptional components, or a bound on the matching number.

An additional audit-only theorem in [EnvironmentAudit.lean](EnvironmentAudit.lean) removes decidability instances from its external interface using classical instances. It obtains a matching whose distinct edges have disjoint, pairwise nonadjacent endpoints in the **original** graph, with the same corrected bound. This checks the endpoint interpretation instead of merely repeating the project's `IsInducedMatching` name. The diagnostic file uses metaprogramming to inspect the environment; it is an audit artifact, not part of the project's mathematical proof.

### Trust boundary

Lean `4.35.0-rc4` was used. The existing toolchain archive's SHA-256 matched the official release metadata:

`fef75506e6af6c3669efc360224410865b3d292240aafc351a312435972667f3`.

The comparison checked 15,337 installed files under its `bin` and `lib` directories against the official archive; every compared file matched. This checks the installed toolchain against the published distribution; it is not a bootstrap proof of the compiler or hardware.

All project modules were rebuilt in a separate output directory, with no previously compiled `StrongEdge` or `StrongEdge19` artifacts on the search path. The nine library dependency checkouts matched the pinned manifest commits and had no tracked modifications. **Previously compiled mathlib and other library artifacts were reused.** This audit does not claim to have rebuilt all of mathlib or independently kernel-checked every imported library artifact. The environment inspection invokes Lean with `-t 0`; that flag is recorded, not presented as a substitute for such a library rebuild.

## Definition correspondence

| Potential mismatch | Inspection and result |
| --- | --- |
| Replacing original conflicts by conflicts in the selected subgraph | [Basic.lean](../../upstream/packing195/lean/StrongEdge/Basic.lean) defines `StrongConflict` using a length-one or length-two walk in the original line graph, with any original edge allowed as the intermediate witness. `candidateConflictGraph` restricts this already-formed conflict graph to `F`. Unselected connecting edges remain effective. |
| "Induced matching" meaning only a matching | [Conflict.lean](../../upstream/packing195/lean/StrongEdge/Conflict.lean) uses pairwise absence of original strong conflict. The audit-only endpoint theorem also checks disjointness and absence of original cross-adjacency. |
| Confusing full and candidate degree | The manuscript's `c(e)` is degree in `conflictGraph G`; `d(e)` is degree in its induced graph on `F`. The normalization and rigidity steps keep these separate. Full-neighborhood closure is derived when the two degrees become equal. |
| Truncating a negative deficit to zero | [Compensation.lean](../lean/StrongEdge19/Compensation.lean) defines the deficit in `Int`, with subtraction after conversion. The full exceptional component can therefore contribute minus one. Only the nonnegative excess-coverage expression uses natural subtraction. |
| Making optimality an assumed existence principle | [Tertiary.lean](../lean/StrongEdge19/Tertiary.lean) proves existence by finite minimization. The objectives are maximum cardinality, minimum candidate-degree sum, then minimum full-degree sum. The final theorem existentially obtains this choice. |
| Counting certificates or labelings instead of components | [TwentyCliqueParts.lean](../../upstream/packing195/lean/StrongEdge/Bounds/TwentyCliqueParts.lean) specifies five disjoint pairs and **equalities for all original neighbors**, enforcing the full doubled-cycle component. [TightComponents.lean](../../upstream/packing195/lean/StrongEdge/TightComponents.lean) filters `G.ConnectedComponent` itself and proves equality with the intermediate support count. No labeling multiplicity is counted. |
| Using an incorrect matching-number surrogate | `prescribed_edge_bound19` uses mathlib's independence number of `(conflictGraph G).induce F`. The proof constructs an independent finite set of the matching's size and applies its cardinality bound. This matches the stated original induced-matching number. |

The explicit five-pair certificate is a concrete definition of the intended doubled five-cycle component. It is not packaged as a separate isomorphism to a named canonical `C5[2]` graph, but its neighbor equalities give exactly that structure. This is a definitional presentation choice, not a weakened exceptional class.

## Proof chain and circularity

The mathematical dependency chain is:

1. The pinned foundation supplies full-degree clique thresholds, the selected-subcubic bound, the local-39 estimate, and twenty-clique rigidity/closure.
2. Exact incidence counting gives `2|F| = 39|M| - sum(delta) - R`.
3. Private-set exchanges and tertiary minimization normalize a zero-deficit center. Improved local bounds exclude candidate degrees 20 through 23; the stronger upstream threshold-24 bound excludes 24. Stage 2 exports candidate degree 19.
4. A separate original-graph rigidity argument extends a nineteen-clique with full conflict degrees at least nineteen to a twenty-clique.
5. At a degree-nineteen zero-deficit center, this extension and upstream closure force the full twenty-clique to be selected.
6. With no selected twenty-clique, zero deficit is impossible; nonnegative integer deficits become positive. The incidence identity yields the nineteen bound.
7. Strong induction removes and restores selected twenty-cliques in the same original graph. Each restoration adds 20 selected edges, one matching member and one correction unit. The component-count comparison gives the final theorem.

The import graph is acyclic. More significantly, the environment audit checks transitive declaration dependencies: the Stage 2 candidate-degree endpoint does not depend on the Stage 3 nineteen-clique extension, and neither structural endpoint depends on the final nineteen-packing theorem. The use of the **older twenty-clique rigidity** in the nineteen-clique argument is not circular: that older result has its own upstream proof and does not use the new nineteen-packing result.

The recorded project dependency closures contain 1,201 declarations for the final endpoint, 857 for the Stage 2 endpoint, 449 for the original nineteen-to-twenty extension, and 553 for the critical-center selected-twenty result. These counts include compiler-generated helpers, not just independently stated mathematical lemmas.

### Critical mathematical checks

**The threshold-24 value is thirteen.** The abstract upstream local-39 interface permits a weaker value fourteen, but the zero-deficit witness argument needs the actual thirteen bound. [CriticalNormalization.lean](../lean/StrongEdge19/CriticalNormalization.lean) uses the stronger upstream theorem where necessary. The two interfaces are not silently conflated.

**The improved high-degree bounds have a root premise.** For thresholds 21, 22 and 23, some extension bounds assume a vertex incident with four selected clique edges. The packing argument does not simply assume this vertex exists. [PrivateSubcubic.lean](../lean/StrongEdge19/PrivateSubcubic.lean) handles the alternative, using neighborhood closure to obtain a private-set bound of thirteen. This supplies the missing-root contradiction before invoking the four-edge-root estimates.

**The nineteenth-to-twentieth extension concerns the original graph first.** [NineteenRigidity.lean](../lean/StrongEdge19/NineteenRigidity.lean) derives a closed original support of at most ten vertices. Its complete original edge set has at most twenty edges. Full conflict degree at least nineteen forces twenty edges and the clique property. Candidate membership of the new edge is absent from this theorem's assumptions and conclusion.

**Selection of the twentieth edge is then proved.** [CriticalNineteen.lean](../lean/StrongEdge19/CriticalNineteen.lean) applies the extension to the private nineteen-clique, uses upstream twenty-clique closure to bound the center's full degree by nineteen, and compares it with candidate degree nineteen. Equality forces the full neighborhood to be selected. This prevents a potentially circular assumption of the very missing edge the proof needs.

**Positive deficits are not asserted on exceptional components.** [PositiveDeficits.lean](../lean/StrongEdge19/PositiveDeficits.lean) retains the no-selected-twenty-clique hypothesis. [Main.lean](../lean/StrongEdge19/Main.lean) restores the exceptional cases separately. In particular, the full doubled five-cycle's negative deficit is not discarded.

**Original conflicts survive removal.** The induction changes `F` to `F minus T`; it does not change `G`. Cross-conflict exclusion follows from the proved full-conflict closure of `T`, so deletion never destroys a witness edge improperly.

## Manuscript-to-Lean correspondence and limitations

The consolidated [manuscript](../manuscript/packing19.md) contains a concordance covering all 83 extension declarations in 27 mathematical modules. Its references to 16 upstream declarations were checked, as were the unchanged mathematical source hashes. The principal arguments match the optimized interfaces. In particular, Stage 2 concludes candidate degree nineteen, while the degree-nineteen branch assumes ordinary optimality and recovers the stronger facts it needs later.

The following are real scope distinctions, explicitly disclosed by the project; they are not counterexamples to the main theorem:

| Item | Current status | Effect on the claimed theorem |
| --- | --- | --- |
| Explicit sharpness construction using nineteen of the twenty edges of `C5[2]` | Paper proof and finite examples; no separate Lean sharpness theorem. The construction is mathematically valid: full conflict graph `K20`, matching number one, correction zero. | The upper-bound theorem is formalized; a claim that the sharpness example itself is separately formalized would be too strong. |
| Replacing "maximum independent set" by "maximal independent set" in the counting identity | Paper observation; current Lean statement uses maximum. Maximality gives coverage, so the observation is consistent with the count. | The stronger assumption used by Lean is always available in the final proof. No gap in the endpoint. |
| Historical matching-number-two/three exchange investigations | Not all historical arguments are reproduced line by line in Lean. | The final general packing theorem proves the required conclusions for every matching number without using those historical arguments. |
| Exact cover identities versus one-sided bounds | Paper sometimes gives an exact combinatorial identity where Lean uses the immediate inequality together with other proved counting facts. | Proof decomposition differs, but the sufficient premises and endpoint are preserved. |
| Finite enumerations | Explicit restricted families and regression examples only. | They are not Lean proof certificates and do not establish universality. Universality comes from the Lean structural arguments and the mathematical proof. |

The endpoint is a prescribed-edge induced-matching packing inequality. This audit does not reinterpret it as a proof of an integer strong-edge-coloring bound or of a different weighted statement.

## Reproduced finite checks

The rerun reproduced the historical JSON results exactly, apart from metadata such as timestamps:

- Stage 2: 72 local templates and four examples.
- Stage 3 triangle-root check: 600 graphs.
- Stage 3 core family: 28 type multisets, 1,082 original core graphs, 3,662 candidate sets, and 48 qualifying nineteen-cliques.
- Stage 3 compensation regressions: six examples.

These checks support reproducibility and catch implementation regressions inside their declared families. They do not substitute for the universal arguments or broaden those families into an exhaustive classification of all graphs of maximum degree four.

## Reproduction and repository integrity

At completion of the original audit, its scripts and generated evidence existed only in this new directory. No tracked mathematical source, manuscript, lockfile, or pinned submodule file was changed, and no commit, pull request, or external publication had been made. This directory was subsequently prepared for publication at the user's request; the original verification records remain unchanged. See the [bundle guide](README.md) for the publication context and snapshot-specific reproduction instructions.

The scripts use the existing local Lean installation and pinned dependency cache located by `OLD` and `TOOLCHAIN`/`TC` near their headers. To reproduce on another machine, adjust those paths to the same Lean release and dependency commits. Use a separate checkout at the audited commit and copy this directory into it, as described in the bundle guide. From that checkout's repository root, run:

```text
python route-b/audit-2026-10-11/source_scan.py
python route-b/audit-2026-10-11/check_toolchain.py
python route-b/audit-2026-10-11/independent_audit.py
python route-b/audit-2026-10-11/check_environment.py
python route-b/audit-2026-10-11/finite_and_provenance.py
python route-b/audit-2026-10-11/finalize_evidence.py
```

`check_environment.py` must run after the complete project build. The build records the pinned package identities, source/output hashes, each compiler exit code, and the exact `LEAN_PATH`. Finite checks call the original computation and validator functions while writing independent records, preserving historical result files.

For future hardening, the environment-based declaration inventory could be incorporated into normal verification, and a clean CI job could rebuild library dependencies or verify an authenticated library cache. These would strengthen reproducibility; neither is evidence of a current mathematical defect.

This assessment applies to the pinned snapshot and the stated trust boundary. It is not an unconditional claim of error-free mathematics or of complete formal verification of every historical prose observation.
