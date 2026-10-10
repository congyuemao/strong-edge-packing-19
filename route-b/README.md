# Route B: global compensation and critical configurations

This directory contains Route B derivations, programs, and verification records. The existing 19.5 proof is shared through the pinned `upstream/packing195` submodule at the repository root.

- [Stage 1: exact compensation and critical normalization](notes/route-b-stage1.md)
- [Stage 1 upstream Lean verification](verification/README.md)
- [Stage 2: paper exclusion of the 39-edge obstruction](notes/route-b-stage2.md)
- [Stage 2 template and boundary checks](results/stage2-checks.json)
- [Stage 2 verification program](scripts/check_stage2.py)

## Current mathematical status

Stage 2 gives a paper proof excluding all five parameter rows for `|F|=39`, induced-matching number two, and zero component correction. Combined with the existing 19.5 theorem and exceptional-component removal, this proves the corrected 19 bound on paper for induced-matching number at most two.

For arbitrary matching number, a tertiary-optimal zero-deficit centre must now have candidate and full conflict degree nineteen, a private nineteen-clique, and exactly one shared candidate neighbour. A twice-covered vertex cannot serve two such centres.

For the first `k=3` obstruction (`|F|=58`, `t=0`), the case `R=1` is excluded on paper. The remaining case has `R=0`, private-clique sizes `19,19,18`, and exactly two shared candidates. It remains open.

**None of the new Stage 2 lemmas has been formalized in Lean.** The finite checks cover 72 labelled obstruction-template checks and four exact boundary examples; they are not an exhaustive 39-edge search. The general 19 conjecture remains unproved.

## Reproduce the finite checks

From the repository root, using Python 3.10 or newer and no third-party packages:

```sh
python route-b/scripts/check_stage2.py
```

All conflicts are computed in the supplied original graph, including original edges outside the candidate set.
