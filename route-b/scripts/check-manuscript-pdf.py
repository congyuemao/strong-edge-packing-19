"""Check PDF publishing integrity and completeness, not mathematical validity."""

import hashlib
import json
from pathlib import Path
import re

import pdfplumber
from pypdf import PdfReader


ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = ROOT / "route-b/manuscript"
PDF = DIRECTORY / "packing19.pdf"
SOURCE = DIRECTORY / "packing19.md"
OUTPUT = DIRECTORY / "pdf-validation.json"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compact(text):
    return re.sub(r"\s+", "", text)


def prose_words_present(fragment, words):
    # PDF extraction may interleave subscripts or a running header with a
    # prose line. Match ordered words with a bounded allowance for those
    # insertions, rather than treating extraction order as logical markup.
    wanted = re.findall(r"[A-Za-z]{2,}", fragment.lower())
    for start, word in enumerate(words):
        if word != wanted[0]:
            continue
        position = start + 1
        for word in wanted[1:]:
            try:
                position = words.index(word, position, min(position + 9, len(words))) + 1
            except ValueError:
                break
        else:
            return True
    return False


def validate():
    source = SOURCE.read_text(encoding="utf-8")
    build = json.loads((DIRECTORY / "pdf-build.json").read_text(encoding="utf-8"))
    assert build["pdf_sha256"] == sha256(PDF)
    assert build["manuscript_sha256"] == sha256(SOURCE)
    assert build["builder_sha256"] == sha256(ROOT / "route-b/scripts/build-manuscript-pdf.py")
    reader = PdfReader(PDF)
    assert not reader.is_encrypted
    assert reader.metadata.author == "Congyue Mao"
    assert reader.metadata.title == source.splitlines()[0][2:]
    assert len(reader.pages) == build["pages"]
    assert all(abs(float(p.mediabox.width) - 595.2756) < 0.01 for p in reader.pages)
    assert all(abs(float(p.mediabox.height) - 841.8898) < 0.01 for p in reader.pages)
    assert sum(len(p.images) for p in reader.pages) == 0

    texts, page_records, font_names = [], [], set()
    with pdfplumber.open(PDF) as document:
        for index, page in enumerate(document.pages, 1):
            text = page.extract_text(x_tolerance=2, y_tolerance=3)
            assert text and "\ufffd" not in text and "\x00" not in text
            assert len(page.chars) > 200, f"Unexpected near-empty page {index}"
            assert all(68 <= c["x0"] and c["x1"] <= 527.3 and
                       25 <= c["top"] and c["bottom"] <= 814 for c in page.chars), index
            footer = "".join(c["text"] for c in page.chars if c["top"] > 790)
            assert footer == str(index), (index, footer)
            if index > 1:
                assert text.startswith("Induced matchings in prescribed edge sets")
            fonts = {c["fontname"] for c in page.chars}
            assert all("+TimesNewRoman" in name or "+STIX" in name for name in fonts), fonts
            font_names.update(fonts)
            texts.append(text)
            page_records.append({"page": index, "characters": len(page.chars),
                                 "bounds_check": "passed", "page_number": footer})
    text = "\n".join(texts)
    flattened = compact(text)
    declarations = []
    for path in sorted((ROOT / "route-b/lean/StrongEdge19").glob("*.lean")):
        declarations.extend(re.findall(r"(?m)^(?:noncomputable )?(?:theorem|def) ([A-Za-z0-9_]+)",
                                       path.read_text(encoding="utf-8")))
    assert len(declarations) == len(set(declarations)) == 83
    assert all(name in flattened for name in declarations)
    statements = re.findall(r"\*\*((?:Theorem|Lemma|Corollary|Foundation) \d+\.\d+)", source)
    assert all(compact(name) in flattened for name in statements)
    tags = re.findall(r"\\tag\{([^}]+)\}", source)
    assert all("(" + tag + ")" in flattened for tag in tags)
    assert build["display_equations"] == source.count("$$") // 2 == 41
    for phrase in ["Congyue Mao", "11 October 2026", "AI assistance and verification",
                   "OpenAI generative AI systems", "including Codex",
                   "English exposition and PDF typesetting were reviewed separately",
                   "Appendix A. Correspondence", "Appendix B. Verification", "References"]:
        assert compact(phrase) in flattened, phrase

    # Check unchanged prose fragments between math, links and code. The
    # fragments are robust to equation extraction and PDF line wrapping.
    proof = source.split("## 1. Statement and conventions", 1)[1]
    proof = proof.split("## Appendix A.", 1)[0]
    proof = re.sub(r"\$\$.*?\$\$", "\n", proof, flags=re.S)
    proof = re.sub(r"\$[^$]+\$|`[^`]+`|\[[^\]]+\]\([^)]+\)", "\n", proof)
    proof = re.sub(r"[*#|]", "", proof).replace("–", "-")
    fragments = [x.strip() for x in proof.splitlines() if len(x.strip()) >= 45]
    words = re.findall(r"[A-Za-z]{2,}", text.lower())
    missing = [x for x in fragments if not prose_words_present(x, words)]
    assert not missing, missing

    links = []
    for page in reader.pages:
        for reference in page.get("/Annots", []):
            annotation = reference.get_object()
            action = annotation.get("/A", {})
            if action.get("/S") == "/URI":
                uri = action["/URI"]
                assert uri.startswith("https://github.com/congyuemao/strong-edge-packing-"), uri
                links.append(uri)
    assert len(links) >= 40
    return {
        "status": "passed", "pdf_sha256": sha256(PDF), "manuscript_sha256": sha256(SOURCE),
        "validator_sha256": sha256(Path(__file__)), "pages": len(reader.pages),
        "numbered_statements_found": len(statements), "equation_tags_found": len(tags),
        "source_display_equations_accounted_for_by_builder": build["display_equations"],
        "extension_declarations_found": len(declarations), "proof_prose_fragments_found": len(fragments),
        "external_links": len(links), "raster_images": 0,
        "embedded_text_fonts": sorted(font_names), "page_checks": page_records,
        "scope": "PDF content, provenance, metadata, embedded font use, links, and text bounds. "
                 "Visual review is recorded separately. Not a Lean build or verification of English mathematics.",
    }


if __name__ == "__main__":
    try:
        result = validate()
    except Exception as error:
        OUTPUT.write_text(json.dumps({"status": "failed", "reason": repr(error)}, indent=2) + "\n", encoding="utf-8")
        raise
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "page_checks"}, indent=2))
