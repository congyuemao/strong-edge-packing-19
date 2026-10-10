"""Independent source inventory and clean project compilation for the pinned audit."""
from pathlib import Path
import hashlib, json, os, re, subprocess, time

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'strong-edge-lean-verification' / 'strong_edge_lean_starter'
TOOLCHAIN = OLD.parent / '.tools' / 'lean-4.35.0-rc4-windows'
LEAN = TOOLCHAIN / 'bin' / 'lean.exe'
BUILD = OUT / 'clean-build'
BUILD.mkdir(exist_ok=True)
roots = [ROOT / 'upstream/packing195/lean', ROOT / 'route-b/lean']
modules = {}
for root in roots:
    for p in root.rglob('*.lean'):
        if any(x.startswith('.') for x in p.relative_to(root).parts):
            continue
        modules['.'.join(p.relative_to(root).with_suffix('').parts)] = (root, p)
imports = {n: re.findall(r'(?m)^(?:public )?import (\S+)\s*$', p.read_text(encoding='utf-8')) for n, (_, p) in modules.items()}
ordered, active, visited = [], set(), set()
def visit(n):
    if n in active:
        raise RuntimeError('Import cycle: ' + n)
    if n in visited:
        return
    active.add(n)
    for dep in imports[n]:
        if dep in modules:
            visit(dep)
        elif dep.startswith(('StrongEdge.', 'StrongEdge19.')):
            raise RuntimeError('Missing project dependency: ' + dep)
    active.remove(n)
    visited.add(n)
    ordered.append(n)
for n in sorted(modules):
    visit(n)

def cmd(*args, cwd=ROOT):
    r = subprocess.run(list(map(str, args)), cwd=cwd, capture_output=True, text=True, encoding='utf-8', errors='replace')
    if r.returncode:
        raise RuntimeError(r.stderr)
    return r.stdout.strip()
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((roots[0] / 'lake-manifest.json').read_text())
packages = []
for p in manifest['packages']:
    directory = OLD / '.lake/packages' / p['name']
    actual = cmd('git', '-C', directory, 'rev-parse', 'HEAD')
    status = cmd('git', '-C', directory, 'status', '--porcelain', '--untracked-files=no')
    packages.append({'name':p['name'], 'expected':p['rev'], 'actual':actual, 'tracked_status':status})
    if actual != p['rev'] or status:
        raise RuntimeError('Package does not match pinned clean source: ' + p['name'])
env = os.environ.copy()
env['PATH'] = str(TOOLCHAIN / 'bin') + os.pathsep + env['PATH']
env['LEAN_PATH'] = os.pathsep.join([str(BUILD)] + [str(OLD / '.lake/packages' / p['name'] / '.lake/build/lib/lean') for p in manifest['packages']])
record = {
    'status':'running', 'repository_commit':cmd('git','rev-parse','HEAD'),
    'upstream_commit':cmd('git','-C',ROOT/'upstream/packing195','rev-parse','HEAD'),
    'lean_version':cmd(LEAN,'--version'), 'module_count':len(modules),
    'source_line_count':sum(len(p.read_text(encoding='utf-8').splitlines()) for _,p in modules.values()),
    'imports':imports, 'topological_order':ordered, 'acyclic':True,
    'packages':packages, 'lean_path':env['LEAN_PATH'],
    'source_hashes':{str(p.relative_to(ROOT)).replace('\\','/'):digest(p) for _,p in modules.values()},
    'scope':'All project Lean modules compiled from pinned source into an initially empty directory. Pinned mathlib and other library compilation artifacts are reused; no project compilation artifacts are reused.',
    'modules':[]}
def save():
    (OUT / 'clean-build-results.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
save()
with (OUT / 'clean-build.log').open('w',encoding='utf-8') as log:
    for i,n in enumerate(ordered):
        root,p = modules[n]
        output = BUILD / (n.replace('.','/') + '.olean')
        output.parent.mkdir(parents=True,exist_ok=True)
        args = [str(LEAN), '-R', str(root), '-o', str(output), str(p)]
        print(f'[{i+1}/{len(ordered)}] {n}',flush=True)
        start = time.monotonic()
        r = subprocess.run(args,cwd=root,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
        log.write(f'\nMODULE {n}\nCOMMAND {args!r}\n{r.stdout}{r.stderr}\nEXIT {r.returncode}\n')
        log.flush()
        record['modules'].append({'name':n,'exit_code':r.returncode,'seconds':round(time.monotonic()-start,3),'olean_sha256':digest(output) if output.exists() else None})
        if r.returncode:
            record['status']='failed';save();print(r.stdout+r.stderr,flush=True);raise SystemExit(r.returncode)
        save()
    changed = [p for p,h in record['source_hashes'].items() if digest(ROOT/p)!=h]
    record['changed_sources']=changed
    record['status']='passed' if not changed else 'failed'
    save()
print('FINISHED: '+record['status'],flush=True)
