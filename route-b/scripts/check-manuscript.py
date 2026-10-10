"""Validate manuscript references and preservation of the audited Lean source.

This checks documentation structure and provenance, not mathematical prose.
"""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[2]
ROUTE = ROOT / "route-b"
MANUSCRIPT = ROUTE / "manuscript/packing19.md"
OUTPUT = ROUTE / "manuscript/validation.json"
CODE_COMMIT = "2c20ac6099a0fb581367e3bee39465aafec5f879"
DECLARATION = re.compile(r"(?m)^(?:noncomputable )?(?:theorem|def) ([A-Za-z0-9_]+)")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def validate():
    body = MANUSCRIPT.read_text(encoding="utf-8")
    verified = json.loads((ROUTE / "verification/interface-refactor/candidate/results.json").read_text(encoding="utf-8"))
    assert verified["status"] == "passed"
    for item in verified["source_hashes"]:
        path = ROUTE / item["path"]
        assert sha256(path.read_bytes()) == item["sha256"], path
        committed = git("show", f"{CODE_COMMIT}:{path.relative_to(ROOT).as_posix()}")
        assert sha256(committed) == item["sha256"], path
    assert git("-C", "upstream/packing195", "rev-parse", "HEAD").decode().strip() == verified["upstream_commit"]
    assert not git("-C", "upstream/packing195", "status", "--porcelain")

    sources = sorted((ROUTE / "lean/StrongEdge19").glob("*.lean"))
    declarations = {p.stem: DECLARATION.findall(p.read_text(encoding="utf-8")) for p in sources}
    declarations = {module: names for module, names in declarations.items() if names}
    concordance = body.split("### A.2. Extension modules", 1)[1].split("### A.3.", 1)[0]
    rows = re.findall(r"(?m)^\| (.+?) \| \[([A-Za-z0-9]+)\.lean\]\(([^)]+)\) \| (.+) \|$", concordance)
    assert len(rows) == len(declarations)
    matched = set()
    for section, module, link, names in rows:
        assert module not in matched
        matched.add(module)
        assert (MANUSCRIPT.parent / link).resolve() == (ROUTE / f"lean/StrongEdge19/{module}.lean").resolve()
        assert re.findall(r"`([A-Za-z0-9_]+)`", names) == declarations[module], module
    assert matched == set(declarations)
    declaration_count = sum(map(len, declarations.values()))
    assert declaration_count == verified["declaration_count"] == 83
    audit_names = {item["declaration"] for item in verified["axiom_audits"]}
    assert {"StrongEdge19." + name for names in declarations.values() for name in names} == audit_names

    upstream_names = set()
    for source in (ROOT / "upstream/packing195/lean/StrongEdge").rglob("*.lean"):
        upstream_names.update(DECLARATION.findall(source.read_text(encoding="utf-8")))
    foundation = body.split("### A.1. Established upstream results", 1)[1].split("### A.2.", 1)[0]
    upstream_references = set(re.findall(r"`([A-Za-z0-9_]+)`", foundation)) - {"StrongEdge"}
    assert upstream_references <= upstream_names, sorted(upstream_references - upstream_names)

    statements = re.findall(r"\*\*(?:Theorem|Lemma|Corollary|Foundation) (\d+\.\d+)", body)
    assert len(statements) == len(set(statements)), "Repeated statement number"
    references = set(re.findall(r"\b(?:Theorem|Lemma|Corollary|Foundation) (\d+\.\d+)", body))
    assert references <= set(statements), sorted(references - set(statements))
    tags = re.findall(r"\\tag\{([^}]+)\}", body)
    assert len(tags) == len(set(tags)), "Repeated equation tag"
    assert body.count("$$") % 2 == 0
    without_displays = re.sub(r"\$\$.*?\$\$", "", body, flags=re.S)
    assert without_displays.count("$") % 2 == 0
    assert not re.search(r"\b(?:TODO|TBD|FIXME)\b|<!--", body)
    anchors = {
        re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")
        for heading in re.findall(r"(?m)^#{1,6} (.+)$", body)
    }
    for anchor in re.findall(r"\]\(#([^)]+)\)", body):
        assert anchor in anchors, anchor

    filenames = git("ls-files", "--cached", "--others", "--exclude-standard", "-z").decode().split("\0")
    files = [ROOT / name for name in filenames if name and (ROOT / name).is_file()]
    broken, non_english = [], []
    for path in files:
        if path.suffix.lower() not in {".md", ".lean", ".py", ".ps1", ".json", ".toml", ".log", ".txt"}:
            continue
        text = path.read_text(encoding="utf-8-sig")
        if re.search(r"[\u3400-\u4dbf\u4e00-\u9fff]", path.relative_to(ROOT).as_posix() + text):
            non_english.append(path.relative_to(ROOT).as_posix())
        if path.suffix == ".md":
            for link in re.findall(r"\]\(([^)\n]+)\)", text):
                if "://" in link or link.startswith(("#", "mailto:")):
                    continue
                target = link.split("#")[0].strip("<>")
                resolved = (path.parent / target).resolve()
                if target and not resolved.exists() and resolved != OUTPUT.resolve():
                    broken.append([path.relative_to(ROOT).as_posix(), target])
    assert not broken, broken
    assert not non_english, non_english
    return {
        "status": "passed",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "mathematical_source_commit": CODE_COMMIT,
        "upstream_commit": verified["upstream_commit"],
        "manuscript_sha256": sha256(MANUSCRIPT.read_bytes()),
        "validator_sha256": sha256(Path(__file__).read_bytes()),
        "verified_source_hashes_unchanged": len(verified["source_hashes"]),
        "existing_lean_files_in_audit": verified["lean_source_file_count"],
        "existing_axiom_audits": verified["axiom_audit_count"],
        "mapped_extension_modules": len(matched),
        "mapped_extension_declarations": declaration_count,
        "upstream_declaration_references_checked": len(upstream_references),
        "numbered_paper_statements": len(statements),
        "numbered_equations": len(tags),
        "manuscript_lines": len(body.splitlines()),
        "maintained_files_scanned": len(files),
        "broken_local_links": broken,
        "cjk_findings": non_english,
        "scope": "Documentation references, English-text scan, math delimiter balance, and source provenance. Not verification of the English proof or a new Lean build.",
    }


if __name__ == "__main__":
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    try:
        result = validate()
    except Exception as error:
        OUTPUT.write_text(json.dumps({"status": "failed", "reason": repr(error)}, indent=2) + "\n", encoding="utf-8")
        raise
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
