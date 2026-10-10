"""Rerun the existing finite checks without overwriting their historical records."""

from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform

import check_stage2 as stage2
import check_stage3 as stage3


ROOT = Path(__file__).resolve().parents[1]


def main():
    templates = stage2.check_templates()
    examples = stage2.check_examples()
    counts = dict(Counter(item["template"] for item in templates))
    assert counts == {
        "double_four_cycle": 24,
        "triple_attached_to_double_path": 24,
        "triple_edge_disjoint_from_double_path": 24,
    }
    fresh = {
        "stage2": {"template_counts": counts, "templates": templates, "examples": examples},
        "stage3": {
            "triangle_roots": stage3.check_triangle_roots(),
            "saturated_families": stage3.check_saturated_families(),
            "compensation_examples": stage3.check_compensation_examples(),
        },
    }
    for stage, values in fresh.items():
        historical = json.loads((ROOT / f"results/{stage}-checks.json").read_text())
        # JSON round-trip normalizes tuple/list representations for exact comparison.
        assert json.loads(json.dumps(values)) == {key: historical[key] for key in values}
    sources = [Path(__file__), Path(stage2.__file__), Path(stage3.__file__)]
    record = {
        "status": "passed",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "python_version": platform.python_version(),
        "script_sha256": {
            p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources
        },
        "historical_results_exactly_reproduced": ["stage2-checks.json", "stage3-checks.json"],
        "stage2_template_count": len(templates),
        "stage2_examples": len(examples),
        "stage3_triangle_roots": fresh["stage3"]["triangle_roots"]["original_graphs_checked"],
        "stage3_family_counts": fresh["stage3"]["saturated_families"]["counts"],
        "stage3_compensation_examples": len(fresh["stage3"]["compensation_examples"]),
        "scope": "Finite regression checks of the existing stated families only; not a formal proof or an exhaustive graph search.",
    }
    output = ROOT / "verification/interface-refactor/candidate/finite-regressions.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
