# Route B: global compensation and critical configurations

This directory contains Route B derivations, programs, and verification records. The existing 19.5 proof is shared through the pinned `upstream/packing195` submodule at the repository root.

- [Stage 1: exact compensation and critical normalization](notes/route-b-stage1.md)
- [Stage 1 upstream Lean verification](verification/README.md)
- [Stage 2: paper exclusion of the 39-edge obstruction](notes/route-b-stage2.md)
- [Stage 2 template and boundary checks](results/stage2-checks.json)
- [Stage 2 verification program](scripts/check_stage2.py)
- [Stage 3: critical-clique rigidity and general compensation](notes/route-b-stage3.md)
- [Stage 3 finite template checks](results/stage3-checks.json)
- [Stage 3 verification program](scripts/check_stage3.py)
- [Lean extension and remaining proof obligations](lean/README.md)
- [New Lean build and axiom audit](verification/lean-extension/README.md)
- [Formalization checkpoint and proof adaptation](notes/lean-formalization-progress.md)

## Current mathematical status

Stage 2 gives a paper proof excluding all five parameter rows for `|F|=39`, induced-matching number two, and zero component correction. Combined with the existing 19.5 theorem and exceptional-component removal, this proves the corrected 19 bound on paper for induced-matching number at most two.

For arbitrary matching number, a tertiary-optimal zero-deficit centre must now have candidate and full conflict degree nineteen, a private nineteen-clique, and exactly one shared candidate neighbour. A twice-covered vertex cannot serve two such centres.

Stage 3 proves a new rigidity statement on paper: a strong clique of nineteen edges, each with full conflict degree at least nineteen, lies in a whole original `C5[2]` component. A zero-deficit private clique would therefore force a fully selected exceptional component. After removing those components from the candidate set, every deficit is at least one.

Consequently `sum delta + R >= |M|` holds for arbitrary matching number, proving the corrected 19 bound on paper. This also excludes the remaining `19,19,18` private-clique configuration from Stage 2.

**Lean formalization is in progress.** The exact compensation identity, tertiary normalization, Stage 3 nineteen-clique rigidity, and exclusion of critical degree nineteen are checked in the new extension. The Stage 2 exclusions for critical degrees twenty through twenty-three remain paper results. The full corrected 19 theorem is not yet formalized; the existing complete packing endpoint remains the corrected 19.5 theorem.

Stage 2 finite checks cover 72 labelled obstruction templates and four exact boundary examples. Stage 3 checks 600 triangle-root graphs, 1,082 saturated original core graphs with 3,662 candidate sets, and six compensation examples. In the saturated families, all 48 qualifying nineteen-cliques lie in original doubled-cycle components. These counts describe the programs' explicit scopes, not an exhaustive search over all original graphs.

## Reproduce the finite checks

From the repository root, using Python 3.10 or newer and no third-party packages:

```sh
python route-b/scripts/check_stage2.py
python route-b/scripts/check_stage3.py
```

All conflicts are computed in the supplied original graph, including original edges outside the candidate set.
