# Stage 1 upstream verification

The files `results.json`, `build.log`, and `audit195-unconditional.log` are actual outputs of [the verification script](../scripts/verify-upstream.ps1).

Pinned upstream commit: `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`.
Lean version: `4.35.0-rc4`. The mathlib revision is fixed by the upstream dependency manifest.

The run used an existing local upstream checkout with compiled caches. It first compared all 75 Lean files and four environment/launcher files against the pinned source, then ran:

```text
lake build
lake env lean StrongEdge/Audit195Unconditional.lean
```

The script recorded raw output, exit codes, source hashes, and axiom results. It checked the same 79 file hashes again after the run. Allowed axioms were exactly `propext`, `Classical.choice`, and `Quot.sound`. Audit declaration names were matched against the source, including parsing multiline axiom lists.

This is an **incremental build and axiom audit of the existing 19.5 development**. It is not a clean-cache rebuild of all dependencies and does not formally certify the new paper lemmas. No new Lean proof placeholders or mathematical axioms were introduced.

The optional project parameter can select another byte-identical upstream `lean/` directory with dependencies already prepared. Its default is the pinned submodule. A clean submodule requires dependency preparation according to the upstream instructions. If the toolchain parameter is omitted, the pinned `lean` and `lake` executables must already be on `PATH`.

From the repository root:

```powershell
./route-b/scripts/verify-upstream.ps1 -ProjectDirectory 'C:/path/to/packing195/lean' -ToolchainBin 'C:/path/to/lean-4.35.0-rc4-windows/bin'
```

These historical logs are retained as produced in Stage 1. Their `scope` field uses the original `notes/route-b-stage1.md` location, now moved under `route-b/`. Relocation does not regenerate historical results.

Stage 1 performed no 39-edge original-graph search. Its logs do not support a claim that the `k=2` configurations were excluded or that the 19 bound was proved. Later mathematical and computational evidence is recorded separately.
