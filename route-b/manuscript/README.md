# Complete English manuscript

- [Typeset PDF](packing19.pdf)
- [Editable mathematical source](packing19.md)
- [Source and Lean correspondence checks](validation.json)
- [PDF build provenance](pdf-build.json)
- [PDF content and layout checks](pdf-validation.json)
- [Visual review](pdf-visual-review.json)

The PDF follows the supplied [19.5 companion manuscript](../../upstream/packing195/manuscript/packing195.pdf): A4 pages, a centred title and subtitle, Congyue Mao's byline, date, abstract and keywords, Times New Roman body text, STIX mathematics, numbered results and equations, a running header, page numbers, and a separate AI-assistance statement before the references. The supplied reference PDF is byte-identical to the pinned upstream copy. Its SHA-256 is `caac492cf24d6abdf28068f0a93f09a66cdeacb12407bdfac04dd36eb81e5144`.

The mathematical source remains `packing19.md`; the builder does not summarize or rewrite the proof. It omits the Markdown navigation links in favour of PDF bookmarks, draws the existing math expressions as vector font glyphs and rules, and reformats the two long concordance tables for the page width. All 83 extension declarations remain present. Local document links become repository hyperlinks. The AI statement follows the reference's disclosure structure and identifies OpenAI generative AI systems, including Codex, without inferring an unverified model identifier from the reference manuscript.

## Reproduce the PDF

Use Python with the versions listed in [pdf-requirements.txt](pdf-requirements.txt), plus the four Times New Roman font files `times.ttf`, `timesbd.ttf`, `timesi.ttf`, and `timesbi.ttf`. On Windows the builder uses the system Fonts directory; elsewhere pass `--font-dir /path/to/fonts`. Font binaries are not redistributed in the repository.

From the repository root:

```sh
python -m pip install -r route-b/manuscript/pdf-requirements.txt
python route-b/scripts/build-manuscript-pdf.py
python route-b/scripts/check-manuscript-pdf.py
python route-b/scripts/check-manuscript.py
```

The builder also accepts an optional local installation in `scratch/pdf-python`. Intermediate inline layout placeholders and rendered page previews belong under ignored `scratch/pdf-review`; the published PDF contains no rasterized equations or placeholder images. The build uses the manuscript's publication date for deterministic PDF metadata.

Render the final PDF with Poppler and inspect every page before publishing:

```sh
pdftoppm -r 105 -png route-b/manuscript/packing19.pdf scratch/pdf-review/page
```

The automatic checker verifies metadata, all numbered statements and equation tags, every Lean declaration in the concordance, substantial prose fragments, hyperlinks, page numbering and text bounds. It does not replace the recorded visual review. None of these publishing checks is a new Lean compilation or a machine verification of the English proof. The audited mathematical source and the pinned 19.5 submodule are unchanged.
