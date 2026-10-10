# New Route B Lean verification

This directory records verification of the independent `route-b/lean/` extension. It is separate from the historical upstream-only evidence in the parent directory.

- [Machine-readable result and source hashes](results.json)
- [Raw compilation and axiom output](build-and-audit.log)
- [Verification script](../../scripts/verify-lean.ps1)
- [Exact mathematical scope and remaining obligations](../../lean/README.md)

The verification recompiles every new module using Lean `4.35.0-rc4`, reusing the previously built, byte-checked upstream development and its pinned mathlib dependency. The upstream source revision is `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`.

Every newly declared theorem and definition is included in the axiom audit. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. Source hashes are checked again after the run.

The checked structural endpoint is nineteen-clique rigidity under full conflict degree at least nineteen. The checked private-set endpoint excludes critical degree nineteen and leaves degrees twenty through twenty-three. **The full corrected nineteen-packing theorem is not yet formalized.**
