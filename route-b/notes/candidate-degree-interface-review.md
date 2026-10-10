# Candidate-degree interface review

Date: 11 October 2026 (Australia/Sydney).

## Assessment and preservation

The proposed interface is mathematically sufficient. The useful change is a clearer separation between Stage 2 critical-degree exclusions and Stage 3 nineteen-clique rigidity. It avoids two applications of the tertiary normalization theorem and weakens the assumptions of the degree-nineteen branch. It does not remove the structural work needed at degrees twenty-one through twenty-three.

The previously verified implementation is preserved at commit `cbc6f7b50f5defb2e03e9291dc3ccac2ff0e7abc`, tagged `strongedge19-verified-original`. The refactor was developed and verified independently on `codex/candidate-degree-interface`, then merged with its complete English manuscript into the default branch, `codex/route-b-stage1`, at the user's request. The pinned 19.5 submodule stays at `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`.

The code reduction is small. This is an auditability refactor, not a new mathematical result or an established build-speed optimization. The tagged baseline and both verification records remain available for comparison. The measurement tables below retain the labels "baseline" and "candidate" for those two checked versions.

## Why the weak interface suffices

Let `H = (conflictGraph G).induce F`, let `M` be maximum with minimum candidate-degree sum, and suppose `e in M`, `delta(e)=0`, and `d_H(e)=19`.

1. The integer deficit definition gives `39 - (19 + 1 + |P_e|) = 0`, hence `|P_e|=19`. No range or normalization theorem is needed for this arithmetic.
2. Maximal cardinality makes `P_e` a clique. Private exchange and minimum degree sum give `d_H(x) >= d_H(e)=19` for every `x in P_e`. Candidate adjacency is induced from the full original conflict graph, so `c_G(x) >= d_H(x) >= 19`.
3. The existing Stage 3 theorem extends the image of `P_e` to an original twenty-clique `T`. Upstream rigidity identifies such a clique as a full original `C5[2]` component. The implementation only needs the existing conflict-closure corollary for `T`.
4. The centre belongs to its private clique, hence to `T`. Conflict closure gives `N_G^conflict(e) subset T minus {e}`, so `c_G(e) <= 19`. Together with `d_H(e)=19 <= c_G(e)`, this gives equality of full and candidate degrees.
5. The candidate neighbourhood is a subset of the full neighbourhood. Their finite cardinalities agree, so all full neighbours of `e` are candidates. The other nineteen members of `T` are such neighbours, and `e` itself is a candidate. Therefore `T subset F`.
6. A hypothesis excluding wholly selected twenty-cliques now contradicts `|T|=20`.

All six steps are in the candidate Lean proof. The original graph remains fixed at every step. No assumption that the twentieth edge was already selected is introduced. Tertiary optimality is not used in this degree-nineteen argument.

## Actual Lean changes

The baseline Lean proof did not literally export the paper's Corollary 6.2. It first excluded degree nineteen, narrowed the remaining degree interval to twenty through twenty-three under the no-twenty-clique hypothesis, and then exported a degree-twenty bundle including full degree and private size. The final lemma excluded degree twenty.

The candidate uses the following order:

```text
Stage 2:
  range + tertiary normalization + private root bounds -> candidate degree <= 20
  high20 clique bound + private exchange              -> candidate degree = 19

Stage 3:
  candidate degree = 19 + ordinary optimality
      -> private size 19 -> nineteen-clique rigidity
      -> full degree = candidate degree -> wholly selected twenty-clique

Final:
  Stage 2 + Stage 3 + no wholly selected twenty-clique -> positive deficit
```

- [CriticalNormalization.lean](../lean/StrongEdge19/CriticalNormalization.lean): only its import changes. All normalization declarations and proofs are preserved. It imports the upstream threshold module directly, instead of obtaining it through Stage 3 rigidity.
- [CriticalHighDegree.lean](../lean/StrongEdge19/CriticalHighDegree.lean): the proof of `zero_deficit_degree_le_twenty` is unchanged. The new `zero_deficit_candidate_degree_eq_nineteen` excludes degree twenty using the existing high20 bound. Its conclusion is only the candidate degree. It has no no-twenty-clique assumption.
- [CriticalNineteen.lean](../lean/StrongEdge19/CriticalNineteen.lean): `critical_degree_nineteen_forces_selected_twenty` requires `IsOptimal` instead of `IsTertiaryOptimal`. Private cardinality comes directly from the deficit; full degree and closure come from rigidity. The obsolete remaining-degree-range wrapper is removed.
- [PositiveDeficits.lean](../lean/StrongEdge19/PositiveDeficits.lean): `zero_deficit_impossible` combines those two interfaces. Its statement and all later mathematical statements are unchanged.
- [Audit.lean](../lean/StrongEdge19/Audit.lean): replaces the two removed declarations with the new one and prints the new interface types.

The removed auxiliary names are `zero_deficit_remaining_degree_range` and `zero_deficit_remaining_degree_twenty`. External code importing those names would need adjustment; preserving unused compatibility wrappers would defeat part of this small simplification. The final public packing statements remain unchanged.

## Measurements and verification

The [comparison record](../verification/interface-refactor/comparison.json) is generated from the preserved baseline commit and candidate source. The [evidence guide](../verification/interface-refactor/README.md) describes reproduction, dependency inspection, timing scope, and regression checks.

| Metric | Preserved baseline | Candidate | Change |
| --- | ---: | ---: | ---: |
| Mathematical Lean lines, excluding audit | 3,023 | 3,014 | -9 |
| All extension Lean lines, including audit | 3,121 | 3,113 | -8 |
| Mathematical declarations | 84 | 83 | -1 |
| Extension Lean files, including audit | 29 | 29 | 0 |
| Calls to full-degree normalization outside its definition | 3 | 1 | -2 |
| `CriticalNormalization` extension module closure, including itself | 13 | 3 | -10 |
| `CriticalHighDegree` extension module closure, including itself | 21 | 17 | -4 |
| `CriticalNineteen` extension module closure, including itself | 14 | 14 | 0 |
| `Main` extension module closure, including itself | 27 | 27 | 0 |
| Degree-nineteen theorem's transitive extension proof dependencies | 38 | 31 | -7 |
| Degree-at-most-twenty theorem's transitive extension proof dependencies | 26 | 26 | 0 |
| Final `prescribed_edge_bound19` transitive extension proof dependencies | 79 | 78 | -1 |
| Full extension rebuild and all-declaration audit, seconds | 344.87 | 344.64 | -0.23 |

The observed time difference is approximately 0.07%, effectively unchanged for a single run of each version. There is no demonstrated compilation-speed benefit. Both runs reuse upstream/mathlib artifacts and recompile all 29 extension files. Diagnostic tools, documentation, and archived evidence add repository lines; the nine-line reduction refers only to mathematical Lean source.

The degree-nineteen proof no longer references `IsTertiaryOptimal`, the private cost/swap chain, `zero_deficit_degree_range`, the full-degree witness, or the zero-deficit normalization theorem. It instead calls the generic finite-neighbourhood equality lemma directly after rigidity. The twenty-one through twenty-three branch has exactly the same direct and transitive extension dependency sets as before. The complete theorem still uses that normalization chain through this branch.

Verification results:

- Full baseline and candidate extension rebuilds passed. Their audits cover all 84 and 83 declarations respectively. Every audited axiom belongs to the unchanged set `propext`, `Classical.choice`, `Quot.sound`; there is no proof placeholder or custom axiom.
- The same seven Lean interface/definition regression examples passed on both versions. They check the final matching-witness and independence-number statements, literal component correction, zero-correction specialization, and unchanged full-original conflict and induced-matching definitions. Four final-theorem axiom prints passed again in that diagnostic.
- The new Stage 2 signature and the weakened degree-nineteen signature are printed in the full candidate audit.
- Stage 2 finite regressions exactly reproduced 72 labelled templates and four boundary examples. Stage 3 exactly reproduced 600 triangle-root graphs, 1,082 original core graphs with 3,662 candidate sets in the stated saturated families, and six compensation examples. The historical result files remain unchanged.
- All 79 upstream source/environment files were byte-compared with the pinned project. The upstream source remains clean. `Main.lean` is byte-identical to the baseline; normalization declarations and the high-degree exclusion proof are unchanged.

The [integrity record](../verification/interface-refactor/candidate/integrity.json) records the pre-merge source-hash, preservation, English-text, and local-link checks. The useful reason to adopt this candidate is the weaker interface and independent stage structure. The measured resource savings alone do not justify the change. The subsequent merge adopts the clearer interface while preserving the original implementation under its tag; it changes no mathematical source relative to the verified candidate.

## Limits of the optimization

No new bound or case exclusion is proved by the refactor. The high20, high21, high22, high23, and nineteen-clique rigidity theorems retain their proofs. The high-degree branch still uses third-level optimization, the full-degree witness, and full-neighbourhood closure. Its elaborated proof dependencies are identical.

Module dependencies and proof dependencies are distinct: an import can be removed from a file even when the complete theorem still needs that module through another branch. The complete packing theorem still needs both tertiary normalization and Stage 3 rigidity. Reusing an already proved theorem twice was not itself a duplicated proof of that theorem; the reduction is in applications and intermediate interfaces.

The main theorem source, the upstream `StrongConflict` and `IsInducedMatching` definitions, and both correction representations are unchanged. The finite checks are regression evidence for their stated families only; the universal conclusion comes from Lean.
