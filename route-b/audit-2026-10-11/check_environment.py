"""Inspect elaborated declarations after the independent source rebuild."""
from pathlib import Path
import json,os,re,subprocess,time
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[1]
OLD=ROOT.parent/'strong-edge-lean-verification/strong_edge_lean_starter'
TC=OLD.parent/'.tools/lean-4.35.0-rc4-windows'
build=json.loads((OUT/'clean-build-results.json').read_text())
assert build['status']=='passed','Wait for the complete source rebuild.'
# Command-only audit files can use Lean's legacy (non-module) format.
# Their declarations are already covered by importing each source module directly.
modules=[n for n in build['topological_order'] if '.Audit' not in n]
header='module\n\n'+'\n'.join('import all '+n for n in modules)+'\nimport Lean.Util.CollectAxioms\nimport Lean.Util.FoldConsts\n\n'
body='''open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let names := env.constants.fold (fun acc n _ =>
    let origin := (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?
    if origin.any (fun m => m.toString.startsWith "StrongEdge." ||
        m.toString.startsWith "StrongEdge19." || m == `StrongEdge || m == `StrongEdge19)
    then acc.push n else acc) (#[] : Array Name)
  for n in names.qsort Name.lt do
    let some info := env.find? n | throwError m!"Missing declaration {n}"
    let axioms ← collectAxioms n
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError m!"Unexpected axiom {ax} in {n}"
    if info.isUnsafe || info.isAxiom then
      throwError m!"Unsafe declaration or project axiom {n}"
    if info.isTheorem && (info.value? (allowOpaque := true)).isNone then
      throwError m!"Theorem body unavailable for dependency inspection: {n}"
    liftIO <| IO.println <| Json.compress <| Json.mkObj [
      ("name", toJson n.toString),
      ("origin_module", toJson ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).get!.toString),
      ("is_theorem", toJson info.isTheorem),
      ("has_body", toJson (info.value? (allowOpaque := true)).isSome),
      ("unsafe", toJson info.isUnsafe),
      ("axioms", toJson (axioms.map Name.toString)),
      ("dependencies", toJson ((info.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)))]

#check @StrongEdge19.prescribed_edge_bound19
#check @StrongEdge19.induced_matching_packing19_with_connected_component_count
#check @StrongEdge19.zero_deficit_candidate_degree_eq_nineteen
#check @StrongEdge19.critical_degree_nineteen_forces_selected_twenty
#check @StrongEdge19.high19_nineteen_clique_extends_to_twenty

namespace IndependentAudit
open Finset StrongEdge StrongEdge19
open scoped Classical
-- No decidability, optimality, connectivity or clique assumptions in the interface.
theorem endpoint_matching_statement {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hDelta : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f →
        ∀ u ∈ e.val, ∀ v ∈ f.val, u ≠ v ∧ ¬ G.Adj u v) ∧
      F.card ≤ 19 * M.card + (tightComponentsIn G F).card := by
  classical
  obtain ⟨M, hMF, hM, hb⟩ := induced_matching_packing19_with_connected_component_count G hDelta F
  refine ⟨M, hMF, ?_, hb⟩
  intro e he f hf hef u hu v hv
  refine ⟨?_, ?_⟩
  · intro huv
    subst v
    exact hM he hf hef (strongConflict_of_shared_endpoint G hef hu hv)
  · intro huv
    exact hM he hf hef (strongConflict_of_adjacent_endpoints G hef hu hv huv)

#check @endpoint_matching_statement
#print axioms endpoint_matching_statement
end IndependentAudit
'''
path=OUT/'EnvironmentAudit.lean'
path.write_text(header+body,encoding='utf-8')
env=os.environ.copy()
env['PATH']=str(TC/'bin')+os.pathsep+env['PATH']
env['LEAN_PATH']=build['lean_path']
args=[str(TC/'bin/lean.exe'),'-t','0','-R',str(OUT),str(path)]
start=time.monotonic()
r=subprocess.run(args,cwd=OUT,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
(OUT/'environment-audit.log').write_text(r.stdout+r.stderr,encoding='utf-8')
if r.returncode:
    print(r.stdout[-6000:]+r.stderr,flush=True)
    raise SystemExit(r.returncode)
entries=[json.loads(s) for s in r.stdout.splitlines() if s.startswith('{') and '"name":' in s]
lookup={e['name']:e for e in entries}
def closure(n):
    seen=set(); todo=[n]
    while todo:
        x=todo.pop()
        if x in seen: continue
        seen.add(x)
        if x in lookup: todo.extend(d for d in lookup[x]['dependencies'] if d in lookup)
    return sorted(seen-{n})
targets=['StrongEdge19.prescribed_edge_bound19','StrongEdge19.zero_deficit_candidate_degree_eq_nineteen',
         'StrongEdge19.critical_degree_nineteen_forces_selected_twenty','StrongEdge19.high19_nineteen_clique_extends_to_twenty']
assert entries and all(n in lookup for n in targets), 'Environment inventory is incomplete.'
deps={n:closure(n) for n in targets}
stage2=deps[targets[1]]
assert targets[3] not in stage2 and not any('NineteenRigidity' in d for d in stage2)
for n in [targets[1],targets[3]]:
    assert not any('packing19_' in d or d=='StrongEdge19.prescribed_edge_bound19' for d in deps[n])
record={'status':'passed','exit_code':r.returncode,'seconds':round(time.monotonic()-start,3),
        'command':args,'trust_argument':0,'declaration_count':len(entries),
        'extension_declaration_count':sum(e['origin_module'].startswith('StrongEdge19.') for e in entries),
        'axioms':sorted({a for e in entries for a in e['axioms']}),
        'no_project_axioms_or_unsafe_declarations':True,
        'all_project_theorem_bodies_available':True,
        'stage2_independent_of_stage3_rigidity':True,
        'main_theorem_not_a_dependency_of_its_structural_lemmas':True,
        'endpoint_matching_wrapper_without_decidability_assumptions':'passed',
        'target_project_dependencies':deps,'declarations':entries}
(OUT/'environment-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['declarations','target_project_dependencies']},indent=2),flush=True)
