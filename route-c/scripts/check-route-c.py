"""Documentation checks for Route C (run from the repository root).

Checks that local links in the Route C documents and the repository README resolve, that the
maintained Route C files contain no CJK characters (English-only policy), that inline and display
math delimiters in the manuscript are balanced, and that every recorded SAT run matches its
expected answer.  It does not re-run the search or verify any mathematical argument."""
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[2]
ROUTE = ROOT / "route-c"
DOCS = [ROOT / "README.md", ROUTE / "README.md", ROUTE / "manuscript" / "eighteen.md",
        ROUTE / "lean" / "README.md"]
RANGES = [(0x3040, 0x30FF), (0x3400, 0x4DBF), (0x4E00, 0x9FFF), (0xAC00, 0xD7AF)]
CJK = re.compile("[" + "".join(chr(a) + "-" + chr(b) for a, b in RANGES) + "]")


def main():
    errors = []
    for doc in DOCS:
        text = doc.read_text(encoding="utf-8")
        for href in re.findall(r"\]\(([^)]+)\)", text):
            if re.match(r"[a-zA-Z]+://", href) or href.startswith("#"):
                continue
            target = (doc.parent / unquote(href.split("#", 1)[0])).resolve()
            if not target.exists():
                errors.append(f"broken link in {doc.relative_to(ROOT)}: {href}")
    for path in ROUTE.rglob("*"):
        if path.is_file() and path.suffix in {".md", ".py", ".json"}:
            if CJK.search(path.read_text(encoding="utf-8", errors="ignore")):
                errors.append(f"non-English characters in {path.relative_to(ROOT)}")
    body = (ROUTE / "manuscript" / "eighteen.md").read_text(encoding="utf-8")
    if body.count("$$") % 2:
        errors.append("unbalanced display math in the manuscript")
    for number, line in enumerate(body.replace("$$", "").splitlines(), 1):
        if line.count("$") % 2:
            errors.append(f"unbalanced inline math on manuscript line {number}")
    if "RESULTS_TABLE_PLACEHOLDER" in body:
        errors.append("results table not filled in")
    record = json.loads((ROUTE / "results" / "sat-results.json").read_text(encoding="utf-8"))
    if not record["all_as_expected"]:
        errors.append("a SAT run does not match its expected answer")
    print(json.dumps({"documents": [str(d.relative_to(ROOT)) for d in DOCS], "sat_runs": len(record["runs"]),
                      "errors": errors}, indent=2))
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
