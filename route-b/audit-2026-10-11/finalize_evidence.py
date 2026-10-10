"""Validate the final report's local references and summarize completed evidence."""
from pathlib import Path
from datetime import datetime, timezone
import importlib.util, json, subprocess

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
spec = importlib.util.spec_from_file_location('manuscript_validator', ROOT / 'route-b/scripts/check-manuscript.py')
validator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(validator)
provenance = validator.validate()
(OUT / 'manuscript-provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')

evidence = {}
for name in ['source-scan', 'clean-build-results', 'environment-audit',
             'toolchain-provenance', 'finite-regressions', 'manuscript-provenance']:
    data = json.loads((OUT / (name + '.json')).read_text())
    assert data['status'] in {'passed', 'no_flagged_tokens'}, (name, data['status'])
    evidence[name] = data

def git(*args, directory=ROOT):
    p = subprocess.run(['git', '-C', str(directory), *args], capture_output=True,
                       text=True, encoding='utf-8', check=True)
    return p.stdout.strip()

commit = git('rev-parse', 'HEAD')
upstream = git('rev-parse', 'HEAD', directory=ROOT / 'upstream/packing195')
assert commit == '028f4d3541ad41a558b3d1f5c8fd962046ea24dd'
assert upstream == '2e91b05b25a4ee931a0490fefcdbb4f253be95c8'
assert not git('status', '--porcelain', '--untracked-files=no')
assert not git('status', '--porcelain', directory=ROOT / 'upstream/packing195')
b = evidence['clean-build-results']
e = evidence['environment-audit']
assert len(b['modules']) == b['module_count'] == 104
assert all(m['exit_code'] == 0 for m in b['modules']) and not b['changed_sources']
assert set(e['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert e['all_project_theorem_bodies_available']
summary = {
    'status': 'passed', 'completed_utc': datetime.now(timezone.utc).isoformat(),
    'repository_commit': commit, 'upstream_commit': upstream,
    'project_modules_recompiled': 104, 'project_source_lines': b['source_line_count'],
    'compiler_seconds': round(sum(m['seconds'] for m in b['modules']), 3),
    'elaborated_project_declarations_checked': e['declaration_count'],
    'elaborated_extension_declarations_checked': e['extension_declaration_count'],
    'transitive_axioms': e['axioms'],
    'source_placeholders_or_escape_tokens': evidence['source-scan']['findings'],
    'tracked_repository_and_upstream_files_unchanged': True,
    'finite_regressions_reproduced': True,
    'library_cache_reused': True,
    'conclusion': 'No substantiated main-theorem proof error, circularity, harmful specification mismatch or additional mathematical axiom found within the documented scope.',
    'report': 'REPORT.md', 'evidence': [name + '.json' for name in evidence],
}
(OUT / 'audit-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
