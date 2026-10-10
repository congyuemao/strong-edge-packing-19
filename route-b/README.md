# Route B: global compensation and critical configurations

This directory contains Route B derivations, programs, and verification records. The existing 19.5 proof is shared through the pinned `upstream/packing195` submodule at the repository root.

The [complete English manuscript](manuscript/packing19.md) is the consolidated proof matching the optimized Lean implementation. A [typeset PDF](manuscript/packing19.pdf) and [publishing instructions](manuscript/README.md) accompany it. The Stage 1–3 notes below preserve the earlier research sequence.

- [Stage 1: exact compensation and critical normalization](notes/route-b-stage1.md)
- [Stage 1 upstream Lean verification](verification/README.md)
- [Stage 2: paper exclusion of the 39-edge obstruction](notes/route-b-stage2.md)
- [Stage 2 template and boundary checks](results/stage2-checks.json)
- [Stage 2 verification program](scripts/check_stage2.py)
- [Stage 3: critical-clique rigidity and general compensation](notes/route-b-stage3.md)
- [Stage 3 finite template checks](results/stage3-checks.json)
- [Stage 3 verification program](scripts/check_stage3.py)
- [Lean extension and main theorems](lean/README.md)
- [New Lean build and axiom audit](verification/lean-extension/README.md)
- [Formalization record and proof adaptations](notes/lean-formalization-progress.md)

## Current mathematical status

The optimized Stage 2 interface says only that a tertiary-optimal zero-deficit centre has candidate degree nineteen. Its twenty-one through twenty-three exclusions retain tertiary normalization and full-neighbourhood closure internally.

Stage 3 proves that a strong clique of nineteen original edges, each with full conflict degree at least nineteen, extends to a twenty-clique in a whole original `C5[2]` component. For a zero-deficit private clique, this rigidity recovers full centre degree nineteen and then forces the twentieth edge into the candidate set. This final branch needs only secondary optimality.

Once wholly selected twenty-cliques are excluded, every deficit is at least one. Exact compensation gives `sum delta + R >= |M|` for arbitrary matching number; induction restores each exceptional component with one correction unit. The manuscript follows this complete proof, including the closed-support argument used by Lean rather than a separate labelled-cycle classification.

**The corrected 19 theorem is now Lean-verified.** The new extension checks the required Stage 2 structural improvements, all five critical-degree exclusions, positive deficits, global compensation, and exceptional-component restoration. `StrongEdge19.prescribed_edge_bound19` states the result using the independence number of the candidate-induced full-original conflict graph and the literal count of fully selected original `C5[2]` connected components. The earlier separate `k=2` and `k=3` exchange arguments are not needed by this formal proof.

Stage 2 finite checks cover 72 labelled obstruction templates and four exact boundary examples. Stage 3 checks 600 triangle-root graphs, 1,082 saturated original core graphs with 3,662 candidate sets, and six compensation examples. In the saturated families, all 48 qualifying nineteen-cliques lie in original doubled-cycle components. These counts describe the programs' explicit scopes, not an exhaustive search over all original graphs.

## Reproduce the finite checks

From the repository root, using Python 3.10 or newer and no third-party packages:

```sh
python route-b/scripts/check_stage2.py
python route-b/scripts/check_stage3.py
```

All conflicts are computed in the supplied original graph, including original edges outside the candidate set.
