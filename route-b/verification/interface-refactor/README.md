# Candidate-degree interface evidence

This directory compares the original verified 19 implementation at `cbc6f7b50f5defb2e03e9291dc3ccac2ff0e7abc` with the separate `codex/candidate-degree-interface` refactor. See the [review](../../notes/candidate-degree-interface-review.md) for the mathematical argument and interpretation.

## Records

Each of `baseline/` and `candidate/` contains:

- `results.json`: full extension rebuild, all-declaration axiom audit, source SHA-256 hashes, and toolchain identity.
- `build-and-audit.log`: raw compiler and axiom output.
- `timing.json`: wall time for one full extension rebuild plus the complete audit, with progress timestamps.
- `regression.log`: final interfaces, unchanged definition checks, and four final-theorem axiom prints.
- `dependencies.log`: elaborated extension-namespace dependencies, read from declaration types and proof bodies.
- `interface-regressions.json`: diagnostic source hashes and Lean exit codes.

The candidate additionally contains `finite-regressions.json`: a rerun of the existing Stage 2 and Stage 3 finite checks, compared exactly with their historical results without overwriting those results.

Its `integrity.json` records a final source-hash comparison, preserved baseline branch and upstream revision, unchanged proof sections, maintained English-text scan, and local Markdown link check.

[comparison.json](comparison.json) records line counts, declaration counts, module closures, proof-dependency differences, and observed build times.

## Measurement scope

Both full verification runs use the same Lean `4.35.0-rc4` toolchain and the same byte-checked compiled upstream/mathlib dependencies. Every extension source file is recompiled, including the audit. There is no concurrent Lean build. The baseline runs first and the candidate second. This is one observation per version, not a controlled repeated benchmark or a claim of statistically significant speedup. Operating-system caches and background activity can affect wall time.

Line counts include comments and blank lines. Mathematical Lean lines exclude `Audit.lean`. Comparison and regression tools live outside the mathematical source tree and are not counted as proof-code reductions; these tools and the retained evidence increase total repository size.

Module closures count only this extension's modules and include the named module itself. Proof closures count referenced extension constants, exclude the named root, and include constants referenced by both types and proof bodies. The diagnostic explicitly uses `import all` so Lean's module system exposes proof implementations; it checks that each inspected root has a proof body. It declares no mathematical constants and is never imported by the mathematical development. Counts omit upstream/mathlib internals and are not the number of axioms or runtime operations.

The baseline dependency inspection ran against the original compiled target proofs before those targets were recompiled with candidate changes. Its only rebuilt prerequisite was the import-only normalization change, whose declaration bodies are unchanged. Baseline and candidate diagnostic source hashes are recorded for comparison.

## Reproduction

First build the pinned upstream package, or use a byte-identical compiled checkout. Then run the following from the repository root, replacing the two local paths:

```powershell
./route-b/scripts/verify-lean.ps1 -UpstreamProject 'C:/path/to/packing195/lean' -ToolchainBin 'C:/path/to/lean-4.35.0-rc4-windows/bin'
./route-b/scripts/check-interface-regressions.ps1 -Label candidate -UpstreamProject 'C:/path/to/packing195/lean' -ToolchainBin 'C:/path/to/lean-4.35.0-rc4-windows/bin'
python route-b/scripts/check-refactor-finite-regressions.py
python route-b/scripts/measure-interface-refactor.py
```

To reproduce the baseline, prepare that commit in a separate checkout, copy only the diagnostic scripts and the two diagnostic Lean files from this directory, build the baseline extension, and use `-Label baseline`. Do not run the dependency diagnostic against stale compiled modules.

`verify-lean.ps1` writes the active result to [lean-extension](../lean-extension/README.md). The saved comparison runs copy its result and raw log into the appropriate evidence subdirectory. Their stopwatch interval covers that verification invocation only, excluding copying records and subsequent regressions. Candidate source hashes, rather than a pre-commit `HEAD`, identify the exact source that was checked.
