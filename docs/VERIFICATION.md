# Verification evidence and reproduction

[Repository overview](../README.md) · [Formalisation](FORMALIZATION.md) · [Research history](RESEARCH_HISTORY.md)

The strongest supported audit conclusion is **no error found within the documented scope**. Formal proof checking, finite computations, manuscript validation, automated audit, and external human peer review are different forms of assessment. The repository does not claim external human refereeing or certified originality.

## Snapshots and trust boundary

The independent audit examined **`028f4d3541ad41a558b3d1f5c8fd962046ea24dd`**, the merge containing the optimised proof and English manuscript. The mathematical source version is `2c20ac6099a0fb581367e3bee39465aafec5f879`. The foundation is pinned to **`2e91b05b25a4ee931a0490fefcdbb4f253be95c8`**.

The audit bundle was published at `b6e81c2fad48c681e8922cf9768c42f40d94f910`, after PDF publication at `cb9ac302a388d10e7c742e58b90ba4c5294a170d`. The later PDF and subsequent documentation changes were not part of the original audit. Its recorded timestamps, paths, hashes, and reproduction requirements remain snapshot-specific.

The report records **104/104 project modules** recompiled from source and **1,521 project-origin declarations** inspected, including private and generated declarations; 327 originate in the extension. The transitive axioms were `propext`, `Classical.choice`, and `Quot.sound`, so the development must not be called axiom-free. Previously compiled mathlib and other library artifacts were reused. The audit does not assert a clean rebuild of the entire dependency graph or a bootstrap verification of Lean and its execution environment.

## Evidence by claim

| Claim | Supporting file | Audit snapshot | Limitation |
| --- | --- | --- | --- |
| Original extension compilation and explicit axiom-audit workflow; retained active record covers 29 Lean files and 83 declarations | [Extension guide](../route-b/verification/lean-extension/README.md), [results](../route-b/verification/lean-extension/results.json) | Source-hash-identified optimised extension at `2c20ac6`; the [baseline archive](../route-b/verification/interface-refactor/baseline/results.json) preserves the first completed version | Recompiled extension only; byte-checked compiled upstream and library dependencies reused. The current record is not the later independent environment inventory. |
| All project modules recompiled and project-origin declarations inspected | [Independent report](../route-b/audit-2026-10-11/REPORT.md), [summary](../route-b/audit-2026-10-11/audit-summary.json), [build results](../route-b/audit-2026-10-11/clean-build-results.json) | `028f4d3` | 104 modules and 1,521 declarations within the stated library-cache trust boundary. These are recorded results, not a new build performed by this documentation reorganisation. |
| Only the three standard transitive axioms; no project axiom or unsafe declaration found | [Environment inspection](../route-b/audit-2026-10-11/environment-audit.json), [source scan](../route-b/audit-2026-10-11/source-scan.json) | `028f4d3` with pinned upstream | Includes private/generated declarations, but is not independent human peer review or an axiom-free result. |
| Historical 19.5 upstream build and axiom check | [Stage 1 verification](../route-b/verification/README.md), [results](../route-b/verification/results.json) | Upstream `2e91b05` | Incremental upstream build; cannot establish the new nineteen-bound proof by itself. |
| Stated finite families reproduce | [Stage 2 results](../route-b/results/stage2-checks.json), [Stage 3 results](../route-b/results/stage3-checks.json), [audit rerun](../route-b/audit-2026-10-11/finite-regressions.json) | Original stages; rerun at `028f4d3` | Restricted templates and boundary examples, not an exhaustive search over graphs and not a universal proof. |
| Manuscript links, declarations, and source hashes correspond | [Recorded validation](../route-b/manuscript/validation.json), [audit provenance](../route-b/audit-2026-10-11/manuscript-provenance.json) | Mathematical source `2c20ac6`; audit at `028f4d3` | Document validation does not independently prove English mathematical prose. |
| PDF publication and layout checks | [Publishing guide](../route-b/manuscript/README.md), [PDF checks](../route-b/manuscript/pdf-validation.json), [visual review](../route-b/manuscript/pdf-visual-review.json) | PDF publication at `cb9ac30`, after the audited snapshot | Separate publishing evidence; no additional Lean compilation or proof certification. |

The finite records cover 72 Stage 2 templates and four examples; Stage 3 covers 600 triangle-root graphs, 1,082 saturated original core graphs with 3,662 candidate sets, and six compensation examples. The 48 qualifying nineteen-cliques occur within those specified families. The [proof guide](PROOF_GUIDE.md) explains the universal structural argument, which does not depend on these tests.

## Reproducing checks without replacing evidence

Use a **disposable checkout or copy** for commands that generate records. The commands below come from the existing guides and scripts; run them from that checkout's repository root. Preserve this publication checkout's historical JSON, logs, PDF, and mathematical sources.

Initialise the recorded submodule revision in the disposable checkout:

```sh
git submodule update --init --recursive
```

Do not use `--remote`. Python 3.10 or newer suffices for the finite checks; they use no third-party packages. The [original finite-check instructions](../route-b/README.md#reproduce-the-finite-checks) give:

```sh
python route-b/scripts/check_stage2.py
python route-b/scripts/check_stage3.py
python route-b/scripts/check-manuscript.py
```

The first two commands rewrite `route-b/results/stage2-checks.json` and `stage3-checks.json`. The manuscript validator rewrites `route-b/manuscript/validation.json`, including its timestamp, even on failure. It also needs Git history containing `2c20ac6` and a clean, initialised upstream submodule. The alternative [finite-regression comparator](../route-b/scripts/check-refactor-finite-regressions.py) compares against historical results but writes `route-b/verification/interface-refactor/candidate/finite-regressions.json`; run that only in isolation too.

For extension verification, prepare Lean **4.35.0-rc4** and the pinned dependency versions. The recorded PowerShell workflow uses Windows executables and explicit local paths to a byte-identical compiled upstream project and toolchain. Replace the example paths, following the [Lean build guide](../route-b/lean/README.md):

```powershell
./route-b/scripts/verify-lean.ps1 -UpstreamProject 'C:/path/to/packing195/lean' -ToolchainBin 'C:/path/to/lean-4.35.0-rc4-windows/bin'
```

This recompiles the extension and rewrites its active verification JSON and log. It reuses prepared upstream/library artifacts; a new clone alone does not supply them. PDF reproduction has separate Python-package and font requirements in the [publishing guide](../route-b/manuscript/README.md#reproduce-the-pdf) and also generates recorded files.

For the independent audit, follow the [snapshot-specific bundle instructions](../route-b/audit-2026-10-11/README.md#reproducing-the-recorded-audit): use a separate checkout at the full audited SHA above, initialise its pinned submodule, and copy the published audit directory into the same relative location. Adjust `OLD`, `TOOLCHAIN`/`TC`, dependency-cache, and archive paths in that disposable copy to the documented versions. Then follow the [report's command sequence](../route-b/audit-2026-10-11/REPORT.md#reproduction-and-repository-integrity):

```sh
python route-b/audit-2026-10-11/source_scan.py
python route-b/audit-2026-10-11/check_toolchain.py
python route-b/audit-2026-10-11/independent_audit.py
python route-b/audit-2026-10-11/check_environment.py
python route-b/audit-2026-10-11/finite_and_provenance.py
python route-b/audit-2026-10-11/finalize_evidence.py
```

Environment inspection must follow the complete project build. Finalisation checks the exact audited HEAD and an otherwise clean tracked checkout. Running these scripts on the later publication commit is not a reproduction of that original audit.
