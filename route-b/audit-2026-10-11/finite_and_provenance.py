"""Reproduce the repository checks without replacing historical evidence."""
from pathlib import Path
import importlib.util, json, sys, hashlib
from collections import Counter

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
sys.path.insert(0,str(ROOT/'route-b/scripts'))
import check_stage2 as s2
import check_stage3 as s3
templates, examples = s2.check_templates(), s2.check_examples()
fresh = {'stage2':{'template_counts':dict(Counter(x['template'] for x in templates)),
                   'templates':templates,'examples':examples},
         'stage3':{'triangle_roots':s3.check_triangle_roots(),
                   'saturated_families':s3.check_saturated_families(),
                   'compensation_examples':s3.check_compensation_examples()}}
for stage,values in fresh.items():
    old = json.loads((ROOT/f'route-b/results/{stage}-checks.json').read_text())
    assert json.loads(json.dumps(values)) == {k:old[k] for k in values}
record = {'status':'passed','historical_results_exactly_reproduced':True,
          'stage2_templates':len(templates),'stage2_examples':len(examples),
          'stage3_triangle_roots':fresh['stage3']['triangle_roots']['original_graphs_checked'],
          'stage3_family_counts':fresh['stage3']['saturated_families']['counts'],
          'stage3_compensation_examples':len(fresh['stage3']['compensation_examples'])}
(OUT/'finite-regressions.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2),flush=True)
spec = importlib.util.spec_from_file_location('manuscript_validator',ROOT/'route-b/scripts/check-manuscript.py')
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)
result = v.validate()
(OUT/'manuscript-provenance.json').write_text(json.dumps(result,indent=2)+'\n')
print('Manuscript provenance passed',flush=True)
