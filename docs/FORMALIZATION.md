# From the manuscript to Lean

[Repository overview](../README.md) · [Proof guide](PROOF_GUIDE.md) · [Verification](VERIFICATION.md)

## The definitive endpoint

The final independence-number statement is **`StrongEdge19.prescribed_edge_bound19`** in [Main.lean](../route-b/lean/StrongEdge19/Main.lean). For a finite simple graph with maximum degree at most four and any finite candidate set $F$, it bounds `F.card` by nineteen times the independence number of `(conflictGraph G).induce F`, plus `(tightComponentsIn G F).card`.

The matching-witness version, `StrongEdge19.induced_matching_packing19_with_connected_component_count`, constructs a finite set $M\subseteq F$ satisfying `IsInducedMatching G` and the bound using `M.card`. The endpoint passes from that witness to the independence number. Neither statement assumes connectivity, planarity, triangle-freeness, zero correction, or a small matching number. The usual finite-type and decidability instances are implementation requirements, not additional graph-structural hypotheses.

## Form conflicts before restricting candidates

In upstream [Basic.lean](../upstream/packing195/lean/StrongEdge/Basic.lean), `StrongConflict G e f` uses adjacency or a length-two walk in the original line graph. Its intermediate edge ranges over **all original edges**. `conflictGraph G` has all edges of $G$ as vertices; `candidateConflictGraph G F` restricts this already-defined graph to candidates.

In [Conflict.lean](../upstream/packing195/lean/StrongEdge/Conflict.lean), `IsInducedMatching` requires pairwise absence of original strong conflict. Building the conflict graph after deleting non-candidate edges would lose valid witnesses. The three-edge path example in [Start here](START_HERE.md#the-question) illustrates the difference.

## Count actual original components

[`tightComponentsIn`](../upstream/packing195/lean/StrongEdge/TightComponents.lean) filters `G.ConnectedComponent` itself for the exceptional structure and full edge selection. Its cardinality is exactly the correction in the final theorem. The equality `tightComponentCount_eq_connected_component_count` connects this literal count to the intermediate support-based count used during restoration.

The five-pair certificate in [TwentyCliqueParts.lean](../upstream/packing195/lean/StrongEdge/Bounds/TwentyCliqueParts.lean) specifies disjoint pairs and exact original-neighbour equalities. These equalities describe a whole $C_5[2]$ component, including the absence of neighbours outside it. The certificate is not packaged as an isomorphism to a separately named canonical graph, but describes that same structure. Different valid labellings do not create extra elements of `G.ConnectedComponent` and are not counted again.

## Follow the paper correspondence

The authoritative [Appendix A](../route-b/manuscript/packing19.md#appendix-a-correspondence-with-the-lean-development) maps all **83 extension declarations** across 27 mathematical modules and identifies the upstream interfaces. Use its full concordance alongside the shorter [proof roadmap](PROOF_GUIDE.md). Some helpers implement finite-set bookkeeping rather than a separately numbered paper lemma.

The optimised boundary matters: Stage 2 exports candidate degree nineteen, and Stage 3 extends an original clique without assuming candidate membership of its new edge. The critical-centre application proves that membership afterwards. The [audit's dependency inspection](../route-b/audit-2026-10-11/REPORT.md#proof-chain-and-circularity) records the absence of a reverse dependency from Stage 2 to the nineteen-clique extension.

The explicit sharpness example has no separate Lean theorem, and the historical exchange arguments are not all reproduced individually. The [manuscript's Appendix B](../route-b/manuscript/packing19.md#appendix-b-verification-status-and-scope) and [verification guide](VERIFICATION.md) distinguish these scope limits from the formal upper-bound theorem.

## Proof dependencies and audit entry points

The mathematical dependency is `strong-edge-packing-195`, pinned at **`2e91b05b25a4ee931a0490fefcdbb4f253be95c8`**. Its [source](../upstream/packing195/lean/StrongEdge.lean), [toolchain](../upstream/packing195/lean/lean-toolchain), and [dependency manifest](../upstream/packing195/lean/lake-manifest.json) remain authoritative.

[`StrongEdge19/Audit.lean`](../route-b/lean/StrongEdge19/Audit.lean) is the extension's explicit declaration/axiom audit entry point. The [build guide](../route-b/lean/README.md) describes recompiling the extension and checking the listed declarations.

The separate [`EnvironmentAudit.lean`](../route-b/audit-2026-10-11/EnvironmentAudit.lean) belongs to the independent audit bundle. It inspects elaborated declarations by originating module, including private and generated declarations, and checks an additional endpoint-based matching wrapper. It is an audit artifact, not an ordinary mathematical proof dependency. Its recorded results apply to the earlier audited snapshot identified in [Verification](VERIFICATION.md#snapshots-and-trust-boundary).
