# Route C Lean development

This package formalizes **Proposition 1.1** of the [Route C manuscript](../manuscript/eighteen.md): the circulant $C_9(1,3)$ result. Its namespace is `StrongEdgeRouteC`. It imports the pinned 19.5 foundation (`StrongEdge`), but does not change it or Route B. The definitions of strong conflict, induced matching and $C_5[2]$ component are the upstream ones.

## Checked results

All declarations are in [Circulant.lean](StrongEdgeRouteC/Circulant.lean).

| Result | Principal declaration |
| --- | --- |
| $C_9(1,3)$ is 4-regular with eighteen edges | `circulant913_degree_four`, `circulant913_edge_count` |
| All eighteen edges pairwise conflict | `circulant913_all_edges_strong_clique` |
| Every induced matching has at most one edge; a one-edge induced matching exists | `circulant913_induced_matching_card_le_one`, `circulant913_exists_induced_matching_card_one` |
| No vertex set is a $C_5[2]$ component | `circulant913_no_five_cycle_blowup_component` |
| Refutation of the $m/17$ conjecture: maximum degree four, no $C_5[2]$ component, and $17\lvert M\rvert<m$ for every induced matching $M$ | `circulant913_refutes_m_div_17` |
| Attainment of $m=18\nu_s$ | `circulant913_eighteen_bound_attained` |

Finite facts are proved with kernel-checked `decide`, not `native_decide`. [Audit.lean](StrongEdgeRouteC/Audit.lean) prints the axioms of every declaration.

**Not formalized.** Theorem 1.2 and its consequences are not formalized here. That includes the nineteen-edge strong clique theorem, which depends on the SAT search.

## Build

The toolchain is pinned by [lean-toolchain](lean-toolchain). From this directory:

```sh
lake exe cache get
lake build
lake env lean StrongEdgeRouteC/Audit.lean
```

Dependency resolution clones mathlib at the revision pinned by the upstream project, so the first build needs several gigabytes of disk space.
