"""Compare the candidate-degree interface with the preserved verified baseline."""

import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[2]
BASELINE = "cbc6f7b"
PREFIX = "route-b/lean/"
EVIDENCE = ROOT / "route-b/verification/interface-refactor"


def baseline_sources():
    names = subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", BASELINE, PREFIX], cwd=ROOT, text=True
    ).splitlines()
    return {
        name: subprocess.check_output(["git", "show", f"{BASELINE}:{name}"], cwd=ROOT).decode()
        for name in names if name.endswith(".lean")
    }


def current_sources():
    return {
        p.relative_to(ROOT).as_posix(): p.read_text(encoding="utf-8")
        for p in (ROOT / PREFIX).rglob("*.lean")
        if ".build" not in p.parts and ".lake" not in p.parts
    }


def proof_dependencies(label):
    path = EVIDENCE / label / "dependencies.log"
    if not path.exists():
        return None
    return {
        item["declaration"]: item for line in path.read_text().splitlines()
        if line.startswith("{") for item in [json.loads(line)]
    }


def summarize(sources):
    imports = {}
    for path, text in sources.items():
        module = path[len(PREFIX):-5].replace("/", ".")
        imports[module] = re.findall(r"(?m)^(?:public )?import (StrongEdge19(?:\.[\w]+)*)\s*$", text)

    def closure(module):
        seen = set()
        pending = [module]
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            pending.extend(imports[name])
        return sorted(seen)

    return {
        "lean_files": len(sources),
        "physical_lines_including_audit": sum(len(t.splitlines()) for t in sources.values()),
        "mathematical_lines_excluding_audit": sum(
            len(t.splitlines()) for p, t in sources.items() if not p.endswith("/Audit.lean")
        ),
        "declarations": sum(len(re.findall(
            r"(?m)^(?:noncomputable )?(?:theorem|def) ([A-Za-z0-9_]+)", t
        )) for t in sources.values()),
        "module_dependencies_including_self": {
            name: closure(name) for name in [
                "StrongEdge19.CriticalNormalization", "StrongEdge19.CriticalHighDegree",
                "StrongEdge19.CriticalNineteen", "StrongEdge19.Main",
            ]
        },
        "normalization_calls_outside_its_definition": sum(
            t.count("zero_deficit_full_degree_and_closed_neighborhood")
            for p, t in sources.items()
            if not p.endswith(("/CriticalNormalization.lean", "/Audit.lean"))
        ),
    }


def main():
    before = baseline_sources()
    after = current_sources()
    result = {
        "baseline_commit": subprocess.check_output(
            ["git", "rev-parse", BASELINE], cwd=ROOT, text=True
        ).strip(),
        "baseline": summarize(before), "candidate": summarize(after),
        "changed_mathematical_files": {
            p: {"before_lines": len(before[p].splitlines()), "after_lines": len(after[p].splitlines())}
            for p in before if p in after and before[p] != after[p] and not p.endswith("/Audit.lean")
        },
        "main_source_byte_identical": (ROOT / (PREFIX + "StrongEdge19/Main.lean")).read_bytes() ==
            subprocess.check_output(["git", "show", f"{BASELINE}:{PREFIX}StrongEdge19/Main.lean"], cwd=ROOT),
        "timing_caveat": "One sequential full rebuild per version; includes all-declaration axiom audit. "
            "Reuses cached upstream and mathlib. These are observed wall times, not a statistical speedup claim.",
    }
    for label in ["baseline", "candidate"]:
        timing = EVIDENCE / label / "timing.json"
        if timing.exists():
            result[label]["full_build_and_audit_seconds"] = json.loads(timing.read_text())["elapsed_seconds"]
    old_deps, new_deps = proof_dependencies("baseline"), proof_dependencies("candidate")
    if old_deps is not None and new_deps is not None:
        result["elaborated_proof_dependency_comparison"] = {}
        for root in old_deps:
            old = set(old_deps[root]["transitive_extension_dependencies"])
            new = set(new_deps[root]["transitive_extension_dependencies"])
            result["elaborated_proof_dependency_comparison"][root] = {
                "before_count": len(old), "after_count": len(new),
                "removed": sorted(old - new), "added": sorted(new - old),
                "before_direct": old_deps[root]["direct_extension_dependencies"],
                "after_direct": new_deps[root]["direct_extension_dependencies"],
            }
    output = EVIDENCE / "comparison.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
