# Route B Lean extension

This is an independent extension of the fixed 19.5 development. Its namespace is `StrongEdge19`; the upstream namespace remains `StrongEdge`. The upstream mathematical source, toolchain, and dependency lockfiles are unchanged.

**The full corrected nineteen-packing theorem is not yet formalized.** This checkpoint certifies the exact compensation identity, tertiary normalization of every zero-deficit centre, the new nineteen-clique rigidity theorem, and exclusion of the critical degree-nineteen case. Critical degrees twenty through twenty-three still require the new Stage 2 arguments.

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

All names above have the prefix `StrongEdge19.`. [StrongEdge19.lean](StrongEdge19.lean) imports the checked mathematical development. [Audit.lean](StrongEdge19/Audit.lean) prints representative theorem types and the axioms of every new declaration.

The rigidity theorem assumes that all nineteen clique members have **full original conflict degree** at least nineteen. It does not omit this hypothesis or replace full degrees with selected degrees. The extended twentieth edge need not have belonged to the candidate set. Candidate membership is derived separately using the normalized centre's closed full neighbourhood.

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

## Remaining obligations for the full nineteen theorem

The paper proof's Stage 2 supplies the following arguments, which are still pending in Lean:

1. Improve the all-high20 clique bound from eighteen to seventeen.
2. At a four-selected-edge root, prove the high21, high22, and high23 bounds sixteen, fifteen, and thirteen.
3. Prove that a closed private centre of full degree at least twenty-one has private size at most thirteen when the private selected maximum degree is at most three.
4. Use these facts to exclude the remaining critical centre degrees twenty through twenty-three. The checked endpoint `zero_deficit_remaining_degree_range` states exactly this remaining range when selected twenty-cliques have been excluded.
5. Obtain positive deficits, apply the checked compensation theorem, and restore the wholly selected exceptional components with the exact original correction term.

No theorem asserting the unconditional corrected nineteen bound is present in this extension yet. See the [formalization checkpoint note](../notes/lean-formalization-progress.md) for the proof adaptation used for rigidity.
