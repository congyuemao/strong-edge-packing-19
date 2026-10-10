"""Record a conservative lexical scan of both pinned project source trees."""
from pathlib import Path
import hashlib, json, re

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
roots = [ROOT / 'route-b/lean', ROOT / 'upstream/packing195/lean']
patterns = {
    'proof_placeholder_or_axiom': r'\b(?:sorry|admit|sorryAx|axiom)\b',
    'unsafe_or_native_escape': r'\b(?:unsafe|native_decide|ofReduceBool|ofReduceNat|implemented_by|extern|trustLevel|debug\.skipKernelTC)\b',
    'custom_elaboration_or_opaque': r'\b(?:opaque|run_tac|run_elab|elab_rules|macro_rules|partial)\b|^\s*(?:elab|macro)\b',
}
files = []
findings = []
options = []
for root in roots:
    for path in sorted(root.rglob('*.lean')):
        if any(p.startswith('.') for p in path.relative_to(root).parts):
            continue
        rel = path.relative_to(ROOT).as_posix()
        content = path.read_text(encoding='utf-8')
        files.append({'path': rel, 'lines': len(content.splitlines()),
                      'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
        for number, line in enumerate(content.splitlines(), 1):
            for category, pattern in patterns.items():
                if re.search(pattern, line):
                    findings.append({'file': rel, 'line': number, 'category': category, 'text': line})
            if re.search(r'\bset_option\b', line):
                options.append({'file': rel, 'line': number, 'text': line})
record = {'status': 'no_flagged_tokens' if not findings else 'review_required',
          'scope': 'Lexical scan including comments; not a replacement for elaborated axiom/type inspection.',
          'files_count': len(files), 'lines_count': sum(f['lines'] for f in files),
          'patterns': patterns, 'findings': findings, 'set_options': options, 'files': files}
(OUT / 'source-scan.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: v for k, v in record.items() if k != 'files'}, indent=2))
