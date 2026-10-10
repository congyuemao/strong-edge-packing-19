# Route B Lean extension

This is an independent extension of the fixed 19.5 development. Its namespace is `StrongEdge19`; the upstream namespace remains `StrongEdge`. The upstream mathematical source, toolchain, and dependency lockfiles are unchanged.

**The full corrected nineteen-packing theorem is formalized.** The principal result is `StrongEdge19.prescribed_edge_bound19` in [Main.lean](StrongEdge19/Main.lean):

```lean
F.card ≤ 19 * ((conflictGraph G).induce (F : Set G.edgeSet)).indepNum +
  (tightComponentsIn G F).card
```

Its only graph hypothesis is `∀ x, G.degree x ≤ 4`, in a finite simple graph. All conflicts use `G`, including unselected original edges. The upstream component certificate and connected-component count supply exactly the specified correction. The module also provides an induced-matching witness and the zero-correction specialization.

The [complete English manuscript](../manuscript/packing19.md) follows the optimized proof and maps all 83 extension declarations to the corresponding paper arguments.

## Checked results

| Result | Source | Principal declaration |
| --- | --- | --- |
| Exact coverage count, with integer deficits | [Compensation.lean](StrongEdge19/Compensation.lean) | `compensation_identity` |
| Equivalence of the nineteen bound and compensation | [Compensation.lean](StrongEdge19/Compensation.lean) | `nineteen_bound_iff_compensation` |
| Existence of tertiary optimization and private exchanges | [Tertiary.lean](StrongEdge19/Tertiary.lean) | `tertiary_optimal_exists` |
| Critical degree range, full-degree witness, and closed full neighbourhood | [CriticalNormalization.lean](StrongEdge19/CriticalNormalization.lean) | `zero_deficit_full_degree_and_closed_neighborhood` |
| Independent root neighbourhood at full threshold nineteen | [Root19.lean](StrongEdge19/Root19.lean) | `high19_large_clique_root_neighborhood_independent` |
| Root load budget and exclusion of three triple types | [RootLoad.lean](StrongEdge19/RootLoad.lean) | `high19_no_three_triple_types` |
| Saturated-label and two-triple exclusions | [RootSaturation.lean](StrongEdge19/RootSaturation.lean), [OuterSupport.lean](StrongEdge19/OuterSupport.lean) | `high19_two_triples_outer_card_le_three` |
| Existence and counting of the quadruple core | [QuadType.lean](StrongEdge19/QuadType.lean), [QuadLoad.lean](StrongEdge19/QuadLoad.lean), [QuadCore.lean](StrongEdge19/QuadCore.lean) | `high19_large_quad_counts` |
| A closed original support with at most ten vertices | [ClosedCore.lean](StrongEdge19/ClosedCore.lean) | `high19_large_clique_closed_ten_support` |
| Nineteen-clique extension to a whole doubled five-cycle | [NineteenRigidity.lean](StrongEdge19/NineteenRigidity.lean) | `high19_nineteen_clique_in_five_cycle_blowup` |
| Degree-nineteen critical centres force a wholly selected twenty-clique | [CriticalNineteen.lean](StrongEdge19/CriticalNineteen.lean) | `critical_degree_nineteen_forces_selected_twenty` |
| Full-degree-at-least-twenty strong cliques have at most seventeen edges | [High20Root.lean](StrongEdge19/High20Root.lean) | `high20_clique_card_le_seventeen` |
| Four-selected-edge root bounds at thresholds twenty-one, twenty-two, and twenty-three | [SmallTypes.lean](StrongEdge19/SmallTypes.lean), [High22Root.lean](StrongEdge19/High22Root.lean), [High23Root.lean](StrongEdge19/High23Root.lean) | `high21_clique_card_le_sixteen_of_root_four`, `high22_clique_card_le_fifteen_of_root_four`, `high23_clique_card_le_thirteen_of_root_four` |
| Closed high-degree private centres with selected maximum degree three have private size at most thirteen | [PrivateSubcubic.lean](StrongEdge19/PrivateSubcubic.lean) | `private_subcubic_card_le_thirteen` |
| Stage 2 candidate-degree interface for zero deficit | [CriticalHighDegree.lean](StrongEdge19/CriticalHighDegree.lean) | `zero_deficit_candidate_degree_eq_nineteen` |
| Elimination of zero deficit using Stage 3 rigidity | [PositiveDeficits.lean](StrongEdge19/PositiveDeficits.lean) | `zero_deficit_impossible` |
| Positive deficits and the global compensation inequality | [PositiveDeficits.lean](StrongEdge19/PositiveDeficits.lean) | `deficit_pos_of_no_twenty_clique`, `global_compensation_of_no_twenty_clique` |
| Unconditional corrected nineteen packing and the independence-number form | [Main.lean](StrongEdge19/Main.lean) | `induced_matching_packing19_with_connected_component_count`, `prescribed_edge_bound19` |

All names above have the prefix `StrongEdge19.`. [StrongEdge19.lean](StrongEdge19.lean) imports the checked mathematical development. [Audit.lean](StrongEdge19/Audit.lean) prints representative theorem types and the axioms of every new declaration.

The rigidity theorem assumes that all nineteen clique members have **full original conflict degree** at least nineteen. It does not omit this hypothesis or replace full degrees with selected degrees. The extended twentieth edge need not have belonged to the candidate set. In the degree-nineteen branch, twenty-clique closure gives full centre degree nineteen; equality with the candidate degree then proves that the entire twenty-clique is selected. This branch requires only `IsOptimal`, not tertiary optimality.

Stage 2 exports only the candidate-degree conclusion. Its exclusions at degrees twenty-one through twenty-three still use tertiary normalization and full-neighbourhood closure internally. Stage 2 has no module dependency on Stage 3 rigidity. See the [interface review and measured comparison](../notes/candidate-degree-interface-review.md).

## Reproduce the recorded verification

Use Lean `4.35.0-rc4` and the dependencies pinned by `upstream/packing195/lean/lake-manifest.json`. First prepare and build that upstream project according to its instructions. A previously built byte-identical checkout is also accepted.

From the research repository root, run:

```powershell
./route-b/scripts/verify-lean.ps1 -UpstreamProject 'C:/path/to/packing195/lean' -ToolchainBin 'C:/path/to/lean-4.35.0-rc4-windows/bin'
```

The script checks the fixed upstream revision and tracked cleanliness, compares all 79 upstream source and environment files, recompiles every extension module, audits every new declaration, and records source hashes before and after compilation. It reuses compiled upstream and mathlib dependencies; this is not a clean rebuild of those dependencies. The checked invocation is `lake env lean` with an explicit extension source root and output directory.

Evidence is saved in [verification/lean-extension](../verification/lean-extension/README.md), separately from the historical upstream-only build. The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. Failed runs write a failed status instead of retaining a stale success record.

For development only, `build-lean.ps1` accepts `-Module StrongEdge19.ModuleName` and optional `-Incremental`. The recorded verification deliberately omits that option. Generated `.build/` and `.lake/` files are ignored by Git.

The local `lakefile.toml` also declares the extension's path dependency on the fixed upstream package. The recorded build uses the script above so that no second dependency download or modification of the fixed package is needed.

## Scope of the completed proof

The full theorem has no remaining formal proof obligations. The stronger pointwise deficit statement applies to tertiary-optimal maximum independent sets after fully selected twenty-cliques are excluded. The final cardinality bound is expressed using the independence number, so it is independent of which maximum independent set represents that number.

The threshold twenty-one through twenty-three improvements listed above explicitly require a four-selected-edge root. The proof supplies that root for a large critical private clique using the separate closed-centre lemma; it does not assert those improvements for every abstract clique.

The proof does not rely on the finite template checkers. The historical Stage 2 exchange analyses for small matching number and the explicit sharpness example are not separately formalized here. The universal main theorem already excludes the proposed 39-candidate, matching-number-two obstruction; `candidate_card_le_thirty_eight_of_indepNum_le_two` records this corollary. See the [formalization record](../notes/lean-formalization-progress.md) for adaptations of the paper proof.
