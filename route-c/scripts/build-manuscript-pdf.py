"""Typeset the complete English manuscript in the companion 19.5 PDF style.

All proof prose is read from route-c/manuscript/eighteen.md. Equations are drawn as embedded font
glyphs and vector rules, not raster screenshots. See manuscript/README.md.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
from html import escape
import json
import os
from pathlib import Path
import re
import sys
from urllib.parse import quote


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "route-c/manuscript/eighteen.md"
OUTPUT = ROOT / "route-c/manuscript/eighteen.pdf"
SCRATCH = ROOT / "scratch/pdf-review"
# Dependencies come from an ordinary pip installation of route-b/manuscript/pdf-requirements.txt.

import matplotlib
from matplotlib.font_manager import FontProperties
from matplotlib.mathtext import MathTextParser
from PIL import Image
import reportlab
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY, TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfgen.canvas import Canvas
from reportlab.platypus import (
    BaseDocTemplate, Flowable, Frame, LongTable, PageTemplate, Paragraph as BaseParagraph,
    Spacer, TableStyle,
)


WIDTH, HEIGHT = A4
MARGIN = 69
TEXT_WIDTH = WIDTH - 2 * MARGIN
MATH = MathTextParser("path")
matplotlib.rcParams["mathtext.fontset"] = "stix"
matplotlib.rcParams["mathtext.default"] = "it"
MATH_IMAGES = {}
FONT_NAMES = {}
EQUATION_TAGS = []
DECLARATIONS = []
COUNTS = {"source_blocks": 0, "display_equations": 0, "tables": 0}


class Paragraph(BaseParagraph):
    def draw(self):
        # Inline images are mathematical boxes, not words. Justify against
        # the spaces actually emitted by the text fragments; otherwise the
        # renderer's word count can make these lines exceed the right margin.
        if getattr(self.blPara, "kind", 0) == 1:
            for line in self.blPara.lines:
                line.wordCount = 1 + sum(
                    fragment.text.count(" ") for fragment in line.words
                    if not hasattr(fragment, "cbDefn")
                )
        super().draw()


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def register_fonts(directory):
    for name, filename in [
        ("Paper", "times.ttf"), ("PaperBold", "timesbd.ttf"),
        ("PaperItalic", "timesi.ttf"), ("PaperBoldItalic", "timesbi.ttf"),
    ]:
        path = directory / filename
        if not path.is_file():
            raise FileNotFoundError(f"Required Times New Roman font: {path}")
        pdfmetrics.registerFont(TTFont(name, str(path)))
    pdfmetrics.registerFontFamily(
        "Paper", normal="Paper", bold="PaperBold", italic="PaperItalic",
        boldItalic="PaperBoldItalic",
    )


def font_name(font):
    path = str(font.fname)
    if path not in FONT_NAMES:
        name = "Math" + hashlib.sha256(path.encode()).hexdigest()[:12]
        pdfmetrics.registerFont(TTFont(name, path))
        FONT_NAMES[path] = name
    return FONT_NAMES[path]


def normalize_math(tex):
    tex = tex.replace(r"\bigl", "").replace(r"\bigr", "")
    tex = tex.replace(r"\tfrac12", r"\frac{1}{2}")
    tex = tex.replace(r"\mathbf1", r"\mathbf{1}")
    tex = re.sub(r"\\mathcal\s+([A-Za-z])", r"\\mathcal{\1}", tex)
    return " ".join(tex.split())


@lru_cache(maxsize=None)
def parsed_math(tex, size):
    return MATH.parse("$" + normalize_math(tex) + "$", dpi=72,
                      prop=FontProperties(size=size))


def draw_math(canvas, parsed, x, baseline):
    canvas.saveState()
    canvas.setFillColor(colors.black)
    for glyph in parsed.glyphs:
        font, size, codepoint = glyph[:3]
        ox, oy = glyph[-2:]
        canvas.setFont(font_name(font), float(size))
        canvas.drawString(x + float(ox), baseline + float(oy), chr(codepoint))
    for rx, ry, rw, rh in parsed.rects:
        canvas.rect(x + float(rx), baseline + float(ry), float(rw), float(rh),
                    stroke=0, fill=1)
    canvas.restoreState()


class PaperCanvas(Canvas):
    def drawImage(self, image, x, y, width=None, height=None, **kwargs):
        key = str(getattr(image, "fileName", getattr(image, "_fileName", image)))
        parsed = MATH_IMAGES.get(key)
        if parsed is None:
            return super().drawImage(image, x, y, width=width, height=height, **kwargs)
        draw_math(self, parsed, x, y + float(parsed.depth))
        return float(parsed.width), float(parsed.height)


def math_markup(tex, size):
    parsed = parsed_math(tex, size)
    key = hashlib.sha256(f"{size}:{tex}".encode()).hexdigest()[:20]
    path = SCRATCH / "inline" / (key + ".png")
    if not path.exists():
        Image.new("RGBA", (1, 1), (255, 255, 255, 0)).save(path)
    # The placeholder reserves width and vertical extent. PaperCanvas draws
    # the vector formula at this location instead of embedding the placeholder.
    MATH_IMAGES[str(path)] = parsed
    return (f'<img src="{escape(str(path), quote=True)}" '
            f'width="{float(parsed.width):.4f}" height="{float(parsed.height):.4f}" '
            f'valign="{-float(parsed.depth):.4f}"/>')


def web_link(target):
    if target.startswith(("https://", "http://", "mailto:")):
        return target
    if target.startswith("#"):
        return None
    path_part, _, anchor = target.partition("#")
    path = (SOURCE.parent / path_part).resolve()
    relative = path.relative_to(ROOT).as_posix()
    if relative.startswith("upstream/packing195/"):
        base = "https://github.com/congyuemao/strong-edge-packing-195/blob/"
        url = base + "2e91b05b25a4ee931a0490fefcdbb4f253be95c8/" + relative.split("/", 2)[2]
    else:
        url = "https://github.com/congyuemao/strong-edge-packing-19/blob/main/" + relative
    return quote(url, safe="/:#") + ("#" + anchor if anchor else "")


TOKEN = re.compile(r"\$[^$\n]+\$|`[^`]+`|\[[^\]]+\]\([^)]+\)|\*\*.+?\*\*|(?<!\*)\*[^*]+\*(?!\*)")


def inline(text, size=11):
    parts, start = [], 0
    for match in TOKEN.finditer(text):
        parts.append(escape(text[start:match.start()].replace("–", "-")))
        token = match.group()
        if token.startswith("$"):
            parts.append(math_markup(token[1:-1], size))
        elif token.startswith("`"):
            parts.append('<font name="Paper" size="' + str(size * 0.94) + '">' + escape(token[1:-1]) + "</font>")
        elif token.startswith("["):
            label, target = re.fullmatch(r"\[([^\]]+)\]\(([^)]+)\)", token).groups()
            href = web_link(target)
            label = inline(label, size)
            parts.append(f'<link href="{escape(href, quote=True)}" color="#182838">{label}</link>' if href else label)
        elif token.startswith("**"):
            parts.append("<b>" + inline(token[2:-2], size) + "</b>")
        else:
            parts.append("<i>" + inline(token[1:-1], size) + "</i>")
        start = match.end()
    parts.append(escape(text[start:].replace("–", "-")))
    return "".join(parts).replace("∎", '<font name="Paper">&#9632;</font>')


def make_styles():
    base = ParagraphStyle("Body", fontName="Paper", fontSize=11, leading=14.3,
                          alignment=TA_JUSTIFY, spaceAfter=6, splitLongWords=1,
                          allowWidows=0, allowOrphans=0, autoLeading="max")
    return {
        "body": base,
        "title": ParagraphStyle("Title", parent=base, fontName="PaperBold", fontSize=19,
                                 leading=23, alignment=TA_CENTER, spaceAfter=10),
        "subtitle": ParagraphStyle("Subtitle", parent=base, fontName="PaperItalic",
                                    fontSize=10.5, leading=13, alignment=TA_CENTER, spaceAfter=7),
        "author": ParagraphStyle("Author", parent=base, fontSize=12, leading=15,
                                  alignment=TA_CENTER, spaceAfter=3),
        "date": ParagraphStyle("Date", parent=base, fontSize=10.5, leading=13,
                                alignment=TA_CENTER, spaceAfter=19),
        "abstract": ParagraphStyle("Abstract", parent=base, fontSize=10, leading=12.8,
                                    leftIndent=18, rightIndent=18, spaceAfter=6),
        "keywords": ParagraphStyle("Keywords", parent=base, fontSize=9, leading=11.5,
                                    leftIndent=18, rightIndent=18, spaceAfter=9),
        "h1": ParagraphStyle("Section", parent=base, fontName="PaperBold", fontSize=13,
                              leading=16, alignment=TA_LEFT, spaceBefore=12, spaceAfter=7,
                              keepWithNext=True),
        "h2": ParagraphStyle("Subsection", parent=base, fontName="PaperBold", fontSize=11.3,
                              leading=14.3, alignment=TA_LEFT, spaceBefore=8, spaceAfter=5,
                              keepWithNext=True),
        "table": ParagraphStyle("Table", parent=base, fontSize=9, leading=11.4,
                                 alignment=TA_LEFT, spaceAfter=0),
        "reference": ParagraphStyle("Reference", parent=base, fontSize=10, leading=12.8,
                                     leftIndent=17, firstLineIndent=-17, spaceAfter=8),
        "list": ParagraphStyle("List", parent=base, leftIndent=17, firstLineIndent=-13,
                                spaceAfter=4),
    }


class Equation(Flowable):
    def __init__(self, source):
        super().__init__()
        COUNTS["display_equations"] += 1
        tag = re.search(r"\\tag\{([^}]+)\}", source)
        self.tag = tag.group(1) if tag else None
        if self.tag:
            EQUATION_TAGS.append(self.tag)
        source = re.sub(r"\\tag\{[^}]+\}", "", source).strip()
        source = source.replace(r"\begin{aligned}", "").replace(r"\end{aligned}", "")
        self.lines = [parsed_math(part.replace("&", "").strip(), 11.5)
                      for part in source.split(r"\\") if part.strip()]
        self.line_heights = [max(float(p.height) + 6, 20) for p in self.lines]
        self.width = TEXT_WIDTH
        self.height = sum(self.line_heights) + 3
        self.spaceAfter = 5
        self.spaceBefore = 0
        for parsed in self.lines:
            if float(parsed.width) > TEXT_WIDTH - (42 if self.tag else 0):
                raise ValueError("Equation does not fit without reducing its type size: " + source)

    def draw(self):
        y = self.height
        for parsed, line_height in zip(self.lines, self.line_heights):
            y -= line_height
            draw_math(self.canv, parsed, (self.width - float(parsed.width)) / 2,
                      y + 3 + float(parsed.depth))
        if self.tag:
            self.canv.setFont("Paper", 10)
            self.canv.drawRightString(self.width, self.height / 2 - 3, "(" + self.tag + ")")


def table_cells(line):
    cells, part, math, code = [], [], False, False
    for char in line.strip()[1:-1]:
        if char == "$" and not code:
            math = not math
        elif char == "`" and not math:
            code = not code
        if char == "|" and not math and not code:
            cells.append("".join(part).strip())
            part = []
        else:
            part.append(char)
    cells.append("".join(part).strip())
    return cells


def make_table(lines, styles):
    COUNTS["tables"] += 1
    rows = [table_cells(line) for line in lines]
    rows = [r for r in rows if not all(re.fullmatch(r":?-+:?", c.strip()) for c in r)]
    header = rows[0]
    if header == ["Paper location", "Lean module", "Declarations"]:
        reshaped = [["Manuscript / module", "StrongEdge19 declarations"]]
        for location, module, declarations in rows[1:]:
            names = re.findall(r"`([^`]+)`", declarations)
            DECLARATIONS.extend(names)
            reshaped.append([location + "<br/>" + inline(module, 9),
                             "<br/>".join(escape(n) for n in names)])
        rows = reshaped
        widths = [138, TEXT_WIDTH - 138]
        data = [[Paragraph(("<b>" + c + "</b>") if i == 0 else c, styles["table"])
                 for c in row] for i, row in enumerate(rows)]
    elif header == ["Paper result", "Source", "Principal declaration or interface"]:
        widths = [145, TEXT_WIDTH - 145]
        data = [[Paragraph("<b>Manuscript step</b>", styles["table"]),
                 Paragraph("<b>Upstream source and interface</b>", styles["table"])]]
        for result, source, names in rows[1:]:
            data.append([Paragraph(inline(result, 9), styles["table"]),
                         Paragraph(inline(source, 9) + "<br/>" + inline(names, 9), styles["table"])])
    else:
        if len(header) == 6:
            widths = [TEXT_WIDTH * 0.4] + [TEXT_WIDTH * 0.12] * 5
        elif len(header) == 3:
            widths = [TEXT_WIDTH * 0.29, TEXT_WIDTH * 0.3, TEXT_WIDTH * 0.41]
        else:
            widths = [TEXT_WIDTH / len(header)] * len(header)
        data = [[Paragraph(("<b>" + inline(c, 9) + "</b>") if i == 0 else inline(c, 9), styles["table"])
                 for c in row] for i, row in enumerate(rows)]
    table = LongTable(data, colWidths=widths, repeatRows=1, hAlign="LEFT",
                      spaceBefore=3, spaceAfter=9)
    table.setStyle(TableStyle([
        ("VALIGN", (0, 0), (-1, -1), "TOP"),
        ("LEFTPADDING", (0, 0), (-1, -1), 5),
        ("RIGHTPADDING", (0, 0), (-1, -1), 5),
        ("TOPPADDING", (0, 0), (-1, -1), 4),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#efefef")),
        ("LINEBELOW", (0, 0), (-1, 0), 0.5, colors.HexColor("#707070")),
        ("LINEBELOW", (0, 1), (-1, -1), 0.25, colors.HexColor("#cccccc")),
    ]))
    return table


class ManuscriptDoc(BaseDocTemplate):
    def afterFlowable(self, flowable):
        if isinstance(flowable, Paragraph) and flowable.style.name in {"Section", "Subsection"}:
            title = flowable.getPlainText()
            key = "section-" + hashlib.sha256(title.encode()).hexdigest()[:12]
            self.canv.bookmarkPage(key)
            self.canv.addOutlineEntry(title, key, level=0 if flowable.style.name == "Section" else 1)


def page_decoration(canvas, doc):
    canvas.saveState()
    if doc.page > 1:
        canvas.setFont("PaperItalic", 8.5)
        canvas.setFillColor(colors.HexColor("#555555"))
        canvas.drawString(MARGIN, HEIGHT - 39, "Strong cliques and the eighteen bound")
        canvas.setStrokeColor(colors.HexColor("#aaaaaa"))
        canvas.setLineWidth(0.35)
        canvas.line(MARGIN, HEIGHT - 44, WIDTH - MARGIN, HEIGHT - 44)
    canvas.setFillColor(colors.black)
    canvas.setFont("Paper", 9)
    canvas.drawCentredString(WIDTH / 2, 35, str(doc.page))
    canvas.restoreState()


def build_story(body, styles):
    title = body.splitlines()[0][2:]
    subtitle = re.search(r"(?m)^\*([^*]+)\*$", body).group(1)
    author = re.search(r"\*\*Author:\*\* (.+)", body).group(1)
    date = re.search(r"\*\*Date:\*\* (.+)", body).group(1).rstrip(".")
    title = title.replace(" for Induced", "<br/>for Induced").replace(" in Graphs", "<br/>in Graphs")
    story = [Spacer(1, 4), Paragraph(title, styles["title"]),
             Paragraph(escape(subtitle), styles["subtitle"]),
             Paragraph(escape(author), styles["author"]),
             Paragraph(escape(date), styles["date"])]
    lines = body.split("## Abstract\n", 1)[1].splitlines()
    i, in_abstract, first_abstract, references = 0, True, True, False
    while i < len(lines):
        line = lines[i].strip()
        if not line or line.startswith("**Contents:**"):
            i += 1
            continue
        COUNTS["source_blocks"] += 1
        if line == "$$":
            end = i + 1
            while lines[end].strip() != "$$":
                end += 1
            story.append(Equation("\n".join(lines[i + 1:end])))
            i = end + 1
            continue
        if line.startswith("|"):
            end = i + 1
            while end < len(lines) and lines[end].strip().startswith("|"):
                end += 1
            story.append(make_table(lines[i:end], styles))
            i = end
            continue
        if line.startswith("## "):
            in_abstract = False
            references = line == "## References"
            story.append(Paragraph(inline(line[3:], 13), styles["h1"]))
            i += 1
            continue
        if line.startswith("### "):
            story.append(Paragraph(inline(line[4:], 11.3), styles["h2"]))
            i += 1
            continue
        end = i + 1
        is_list = bool(re.match(r"(?:\d+\.|-) ", line))
        if not is_list:
            while end < len(lines) and lines[end].strip() and not lines[end].startswith(("#", "|", "$$")):
                end += 1
        paragraph = " ".join(x.strip() for x in lines[i:end])
        if paragraph.startswith("**Keywords."):
            style = styles["keywords"]
        elif in_abstract:
            style = styles["abstract"]
            if first_abstract:
                paragraph = "**Abstract.** " + paragraph
                first_abstract = False
        elif is_list:
            style = styles["list"]
        elif references:
            style = styles["reference"]
        else:
            style = styles["body"]
        p = Paragraph(inline(paragraph, style.fontSize), style)
        # Keep a theorem/lemma lead-in with its following equation or list.
        if re.match(r"\*\*(?:Theorem|Lemma|Corollary|Foundation) ", paragraph):
            p.keepWithNext = True
        next_line = next((x.strip() for x in lines[end:] if x.strip()), "")
        if next_line == "$$" or (is_list and re.match(r"(?:\d+\.|-) ", next_line)):
            p.keepWithNext = True
        if len(paragraph) < 180 and next_line.startswith("**Lemma "):
            p.keepWithNext = True
        story.append(p)
        i = end
    return story, author


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--font-dir", type=Path,
                        default=Path(os.environ.get("WINDIR", "C:/Windows")) / "Fonts")
    args = parser.parse_args()
    # Stable metadata uses the manuscript's publication date, not the generic
    # invariant-mode epoch; this also makes repeated builds byte-identical.
    os.environ["SOURCE_DATE_EPOCH"] = str(int(datetime(2026, 10, 30, tzinfo=timezone.utc).timestamp()))
    SCRATCH.mkdir(parents=True, exist_ok=True)
    (SCRATCH / "inline").mkdir(exist_ok=True)
    register_fonts(args.font_dir)
    body = SOURCE.read_text(encoding="utf-8")
    styles = make_styles()
    story, author = build_story(body, styles)
    assert COUNTS["display_equations"] == body.count("$$") // 2
    assert EQUATION_TAGS == re.findall(r"\\tag\{([^}]+)\}", body)
    doc = ManuscriptDoc(str(OUTPUT), pagesize=A4, title=body.splitlines()[0][2:],
                        author=author, subject="Strong cliques and the eighteen bound for induced matchings in graphs of maximum degree four",
                        keywords="induced matching, strong clique, prescribed edge set, SAT, computer-assisted proof",
                        creator="Proof manuscript typesetting", invariant=1,
                        leftMargin=MARGIN, rightMargin=MARGIN,
                        topMargin=61, bottomMargin=60)
    frame = Frame(MARGIN, 60, TEXT_WIDTH, HEIGHT - 121,
                  leftPadding=0, rightPadding=0, topPadding=0, bottomPadding=0)
    doc.addPageTemplates(PageTemplate(id="Paper", frames=frame, onPage=page_decoration))
    doc.build(story, canvasmaker=PaperCanvas)
    result = {
        "status": "built", "manuscript_sha256": sha256(SOURCE),
        "pdf_sha256": sha256(OUTPUT), "builder_sha256": sha256(Path(__file__)),
        "reportlab_version": reportlab.Version, "matplotlib_version": matplotlib.__version__,
        "pages": doc.page, **COUNTS, "equation_tags": EQUATION_TAGS,
        "author": author, "page_size": "A4", "body_font": "Times New Roman",
        "body_font_size_points": 11, "body_leading_points": 14.3,
        "math_font": "STIX", "math_rendering": "Embedded font glyphs and vector rules",
        "scope": "Typesetting provenance, not verification of the English proof or of the SAT computations.",
    }
    (SOURCE.parent / "pdf-build.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
