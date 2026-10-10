# Independent audit evidence, 11 October 2026

Start with the [audit report](REPORT.md) and [machine-readable summary](audit-summary.json).

The audit examined repository commit `028f4d3541ad41a558b3d1f5c8fd962046ea24dd` and upstream commit `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`. It found no substantiated main-theorem proof error, circularity, harmful specification mismatch, or additional mathematical axiom within the documented scope.

The evidence records successful source compilation of all 104 project Lean modules and inspection of 1,521 project-origin declarations, including private and generated declarations. The transitive axioms were exactly `propext`, `Classical.choice`, and `Quot.sound`. Pinned mathlib and other library compilation artifacts were reused; the report states this trust boundary explicitly.

## Contents

- [Source inventory and lexical scan](source-scan.json), reproduced by [source_scan.py](source_scan.py).
- [Per-module build results](clean-build-results.json) and [compiler output](clean-build.log), reproduced by [independent_audit.py](independent_audit.py).
- [Elaborated declarations, axioms and dependency closures](environment-audit.json) and [raw output](environment-audit.log), reproduced by [check_environment.py](check_environment.py). The generated [Lean inspection source](EnvironmentAudit.lean) includes an endpoint-based matching theorem.
- [Official toolchain comparison](toolchain-provenance.json), reproduced by [check_toolchain.py](check_toolchain.py).
- [Finite regression results](finite-regressions.json) and [manuscript correspondence/provenance](manuscript-provenance.json), reproduced by [finite_and_provenance.py](finite_and_provenance.py).
- [Final evidence checks](finalize_evidence.py), which produced the summary.

Raw records retain the original run's timestamps, host paths and audited commit. The local `clean-build/` directory is intentionally excluded from Git; source/output hashes and compiler logs are retained.

## Reproducing the recorded audit

Use a separate checkout at the **audited commit**, initialize its pinned submodule, and copy this audit directory into the same relative location there. The scripts are tied to that snapshot; in particular, `finalize_evidence.py` checks the exact audited HEAD and an otherwise clean tracked checkout. Running it on the later publication commit is not a reproduction of the original audit.

Adjust the local toolchain, dependency-cache and archive paths identified in the report, then run the scripts in the order listed in its reproduction section. Do not replace the preserved JSON and logs in this publication checkout with results from a different snapshot.

## Publication context

This bundle was published after the default branch advanced to `cb9ac30` to add the companion PDF manuscript. The Lean source and pinned upstream were unchanged between that commit and the audited snapshot. The audit's manuscript observations and recorded hashes apply to `028f4d3`; the later PDF publication is outside the original audit's scope.
