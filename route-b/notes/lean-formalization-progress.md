# Lean formalization record

Date: 11 October 2026 (Australia/Sydney).

The [independent Lean extension](../lean/README.md) now proves the unconditional corrected nineteen bound, with the literal original connected-component correction. It checks the Stage 1 identity and normalization, the required Stage 2 structural improvements, Stage 3 nineteen-clique rigidity, all critical-degree exclusions, and the final packing argument. The upstream 19.5 source is unchanged.

The verified normalization has no assumption that the original neighbourhood is already selected. It first finds a private witness at the next threshold, then uses the tertiary exchange to prove equality of full and candidate centre degrees. Equality of the nested finite neighbourhoods then proves full-neighbourhood closure.

The integer definition of deficit retains the negative contribution of a wholly selected exceptional component. The exact compensation identity itself assumes only that the independent set is maximum; it requires neither a degree bound nor removal of exceptional components.

## Adaptation of the Stage 3 paper proof

The formal proof reuses the upstream twenty-clique rigidity theorem through a shorter completion argument.

1. A high19 clique with at least nineteen edges has a four-selected-edge root with independent original neighbourhood. Its original label load is at most five.
2. Three triple types are impossible. In the two-triple case, the saturated-label argument forces at least four outer edges, while the restricted-degree argument forces at most three. A quadruple type therefore exists.
3. A quadruple, a triple, and a third multiple type would exceed the load budget at a shared label. Consequently all other nonempty multiple types are doubles. Counting forces exactly four double tips, twelve original type incidences, and either three or four selected outer edges.
4. With three outer edges, the selected type incidences are saturated, and the upstream four-full-double-tip theorem gives closure in the original graph. With four outer edges, all double tips have two selected outer neighbours; original degree four gives the same closure. The selected clique is therefore supported on a set of at most ten vertices closed under original adjacency.
5. At most twenty original edges lie inside this closed set. Every full conflict neighbour of a selected edge also lies there. A nineteen-clique whose members each have full conflict degree at least nineteen thus extends to a twenty-clique: each member must be adjacent to all nineteen other edges of the closed edge set. There is only one edge outside the original nineteen-clique.
6. The upstream theorem classifies that twenty-clique as the full edge set of a whole original `C5[2]` component.

This avoids a separate explicit classification of labelled four-cycles in the quadruple branch. The endpoint uses full original degrees throughout, including edges that were not selected.

## Connection to critical private cliques

For an optimal centre (maximum independent set with minimum candidate-degree sum) with zero deficit and candidate degree nineteen, the deficit definition gives private size nineteen directly. Private degree monotonicity makes every private member have full conflict degree at least nineteen. Stage 3 rigidity gives a containing original twenty-clique. Upstream twenty-clique closure bounds the centre's full neighbourhood by the other nineteen clique members. Its candidate degree is already nineteen, so its full and candidate degrees agree. Equality of these nested finite neighbourhoods places the entire twenty-clique in the candidate set.

This branch requires no tertiary exchange. The Stage 2 interface `zero_deficit_candidate_degree_eq_nineteen` supplies its candidate-degree hypothesis; `zero_deficit_impossible` combines the two results when wholly selected twenty-cliques have been excluded. Tertiary optimization and full-neighbourhood closure remain necessary inside the exclusions at degrees twenty-one through twenty-three. The [interface review](candidate-degree-interface-review.md) records the comparison with the preserved original implementation.

## Adaptations of the Stage 2 proof

At a four-selected-edge root, the new small-type argument proves at most eight selected type edges at full threshold twenty-one. For distinct disjoint full double types, every selected tip belongs to the union of their two residual original neighbourhoods, so there are at most four selected tips. Three equal full double types instead permit at most five tips. These counts supply the root bounds sixteen, fifteen, and thirteen at thresholds twenty-one, twenty-two, and twenty-three.

The high20 proof establishes the unconditional strong-clique bound seventeen. Its unique-triple branch uses two finite incidence arguments:

1. Three selected outer edges on at most four multiple tips contain an edge whose two endpoints each have two selected outer incidences. Their two type neighbours then saturate their original degrees. A selected edge at the triple must have its other endpoint among those multiple tips, because otherwise it cannot conflict with the saturated edge. All outer edges would lie in a restricted original graph of maximum degree two with a leaf, where a strong clique has at most three edges.
2. Four selected outer edges on at most four multiple tips saturate every tip. Complementary types produce four distinct tips around any selected edge. An outer edge avoiding its endpoints contributes a fifth original edge inside its cover, in addition to the four type edges. The exact original incidence bound then forces full conflict degree at most nineteen, contradicting the threshold twenty.

This avoids a separate enumeration of labelled paths and four-cycles. The quadruple case sharpens the conclusion of the existing upstream argument to one outer edge. The two-triple case uses selected saturation and the already checked nesting obstruction. The small-type case has at most seventeen edges directly.

The private selected-subcubic lemma is also checked: at a closed private centre of full degree at least twenty-one, each centre endpoint has an original edge missing from the private clique. That edge is still a candidate and is covered by another centre. Its other endpoint cannot support any private edge. The two resulting unused vertices in the six-vertex cover leave at most twelve private incidences, plus the centre itself. Thus the private clique has at most thirteen edges. The helper lemmas explicitly allow any original connecting edge as a conflict witness.

## Completed compensation and component restoration

`zero_deficit_impossible` combines the five critical-degree exclusions. The upstream local 39 bound gives nonnegative integer deficits; excluding zero yields `deficit_pos_of_no_twenty_clique`. Summing proves the Route B compensation budget for every tertiary-optimal maximum independent set.

`Packing.lean` applies the exact identity to obtain the nineteen bound when no twenty-clique is wholly selected. `Main.lean` restores such cliques by induction on the candidate set. The original conflict graph stays fixed throughout. Upstream rigidity makes each removed clique conflict-closed, so one of its edges can be added to the remaining matching. Twenty restored candidates cost nineteen units from that matching edge and one unit of correction.

The upstream support-count comparison and connected-component equivalence identify the correction with the number of fully selected original `C5[2]` components. `prescribed_edge_bound19` then expresses the result directly through mathlib's `indepNum` of the candidate-induced original conflict graph. The explicit matching-number-at-most-two corollary bounds the candidate count by thirty-eight when the correction vanishes.

## Evidence and limits

The [verification record](../verification/lean-extension/results.json) identifies the exact source hashes, Lean version, reused upstream revision, and axiom audit scope. The [raw log](../verification/lean-extension/build-and-audit.log) is compiler output, not a hand-written success summary.

The complete corrected nineteen theorem is included in this audit. No computational search replaces a universal structural argument. The old Stage 2 exchange arguments specific to matching numbers two and three are not separate formalized dependencies; the general theorem subsumes their packing conclusions. The explicit sharpness construction remains a paper and finite-check example.
