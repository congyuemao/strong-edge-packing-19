# Repository instructions

- Keep every maintained filename, directory name, document, code comment, generated record, and commit message in English. Mathematical notation and Unicode mathematical symbols are allowed. Conversation with the user may remain in Chinese.
- Translate earlier maintained documentation when needed to preserve this English-only policy. Preserve historical verification output as evidence; it is already in English.
- Store Route B derivations, scripts, and results under `route-b/`, and Route C derivations, scripts, and results under `route-c/`. Keep common upstream material under `upstream/`.
- The upstream submodule is pinned to `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`. Do not change its verified mathematical source, toolchain, or dependency lockfiles as part of new research.
- Distinguish existing Lean theorems, new paper proofs, finite computations, conjectures, and counterexamples. A successful upstream build does not formalize new paper arguments.
- Evaluate all strong conflicts in the complete original graph. Candidate selection never permits discarding outside-candidate conflict witnesses.
- Preserve the correction term for completely selected original `C5[2]` components. Reduce to zero correction explicitly before using nonnegative local deficits.
- Do not introduce `sorry`, `admit`, custom mathematical axioms, or unstated structural assumptions.
- Before committing new research, check local document links, English-language consistency, result provenance, and whether the claims exceed the proved or searched scope.
