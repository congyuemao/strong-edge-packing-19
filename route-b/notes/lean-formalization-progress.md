# Lean formalization checkpoint

Date: 11 October 2026 (Australia/Sydney).

The [independent Lean extension](../lean/README.md) formalizes the central Stage 1 identity and normalization, the Stage 3 nineteen-clique rigidity theorem, and its application to a degree-nineteen critical centre. The new Stage 2 exclusions for degrees twenty through twenty-three remain paper results. Accordingly, the general corrected nineteen bound is still not a Lean theorem.

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

For a tertiary-optimal centre with zero deficit and candidate degree nineteen, the private clique has nineteen members, all of full conflict degree at least nineteen. Rigidity gives a containing original twenty-clique. Its members all conflict with the centre, except the centre itself. Full-neighbourhood closure therefore places the entire twenty-clique in the candidate set.

The checked corollary rules out this case whenever wholly selected twenty-cliques have been excluded. The order of formalization differs from the paper's order: the degree-nineteen case is now checked, while the Stage 2 arguments excluding degrees twenty through twenty-three are still pending.

## Evidence and limits

The [verification record](../verification/lean-extension/results.json) identifies the exact source hashes, Lean version, reused upstream revision, and axiom audit scope. The [raw log](../verification/lean-extension/build-and-audit.log) is compiler output, not a hand-written success summary.

Successful checking of these statements does not certify the remaining Stage 2 proof or the complete corrected nineteen theorem. No computational search is used as a replacement for a universal structural argument in the checked statements.
