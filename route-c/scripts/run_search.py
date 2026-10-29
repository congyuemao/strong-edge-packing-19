"""Run every SAT instance of the manuscript (Section 5) with both solvers and record the results.

Writes route-c/results/logs/<instance>_<solver>.log and route-c/results/sat-results.json.
Instances run in parallel processes.  Usage: python route-c/scripts/run_search.py [--jobs K]"""
import concurrent.futures
import json
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "strong_clique_search.py"
STRONG = ["--sym", "--count", "--lex"]
INSTANCES = (
    [("control-c52-s20", ["10", "20"], "SAT"), ("control-c52-s19", ["10", "19"], "SAT"),
     ("control-c9-s18", ["9", "18"], "SAT"), ("control-s21", ["10", "21"], "UNSAT"),
     ("control-s20-excluded", ["10", "20", "--not-c52"], "UNSAT"),
     ("control-R-s17", ["10", "17", "--regular-check"], "SAT")]
    + [(f"control-strong-{name}", args + STRONG, exp) for name, args, exp in [
        ("c52-s20", ["10", "20"], "SAT"), ("c52-s19", ["10", "19"], "SAT"), ("c9-s18", ["9", "18"], "SAT"),
        ("s21", ["10", "21"], "UNSAT"), ("s20-excluded", ["10", "20", "--not-c52"], "UNSAT")]]
    + [("R", ["10", "19", "--regular-check"], "UNSAT"), ("I10", ["10", "19", "--not-c52"] + STRONG, "UNSAT")]
    + [(f"I{n}", [str(n), "19"] + STRONG, "UNSAT") for n in range(11, 21)]
)


def run(job):
    name, args, expected, solver = job
    t0 = time.time()
    out = subprocess.run([sys.executable, str(SCRIPT)] + args + ["--solver", solver],
                         capture_output=True, text=True)
    text = out.stdout + out.stderr
    (ROOT / "results" / "logs" / f"{name}_{solver}.log").write_text(text, encoding="utf-8")
    first = text.splitlines()[0] if text else ""
    m = re.search(r": (SAT|UNSAT)\s+clauses=(\d+)\s+\[([\d.]+)s\]", first)
    return {"instance": name, "arguments": args, "solver": solver, "expected": expected,
            "result": m.group(1) if m else "ERROR", "clauses": int(m.group(2)) if m else None,
            "solve_seconds": float(m.group(3)) if m else None,
            "wall_seconds": round(time.time() - t0, 1), "as_expected": bool(m and m.group(1) == expected)}


def main():
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 12
    (ROOT / "results" / "logs").mkdir(parents=True, exist_ok=True)
    work = [(n, a, e, s) for n, a, e in INSTANCES for s in ("cadical", "glucose")]
    with concurrent.futures.ProcessPoolExecutor(max_workers=jobs) as pool:
        rows = list(pool.map(run, work))
    import pysat
    record = {"script": "route-c/scripts/strong_clique_search.py", "python": platform.python_version(),
              "pysat_version": pysat.__version__, "solvers": {"cadical": "CaDiCaL 1.5.3 (pysat Cadical153)",
                                                              "glucose": "Glucose 4 (pysat Glucose4)"},
              "all_as_expected": all(r["as_expected"] for r in rows), "runs": rows}
    (ROOT / "results" / "sat-results.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    for r in rows:
        print(f'{r["instance"]:24s} {r["solver"]:8s} {r["result"]:6s} expected {r["expected"]:6s} '
              f'{r["solve_seconds"]}s')
    print("all as expected:", record["all_as_expected"])


if __name__ == "__main__":
    main()
