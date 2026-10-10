"""Compare the existing toolchain archive with official release metadata."""
from pathlib import Path
import hashlib,json,urllib.request,zipfile
OUT=Path(__file__).resolve().parent
TOOLS=OUT.parents[1].parent/'strong-edge-lean-verification/.tools'
url='https://api.github.com/repos/leanprover/lean4/releases/tags/v4.35.0-rc4'
req=urllib.request.Request(url,headers={'User-Agent':'StrongEdge19-independent-audit','Accept':'application/vnd.github+json'})
with urllib.request.urlopen(req,timeout=30) as r:
    metadata=json.load(r)
asset=next(a for a in metadata['assets'] if a['name']=='lean-4.35.0-rc4-windows.zip')
archive=TOOLS/asset['name']
with archive.open('rb') as f:
    actual='sha256:'+hashlib.file_digest(f,'sha256').hexdigest()
assert asset['digest']==actual,(asset['digest'],actual)
compared=[]
with zipfile.ZipFile(archive) as z:
    for name in z.namelist():
        relative=Path(name)
        if name.endswith('/') or len(relative.parts)<2 or relative.parts[1] not in {'bin','lib'}:
            continue
        installed=TOOLS/relative
        assert installed.is_file(),name
        with installed.open('rb') as f:
            disk=hashlib.file_digest(f,'sha256').hexdigest()
        with z.open(name) as f:
            original=hashlib.file_digest(f,'sha256').hexdigest()
        assert disk==original,name
        compared.append(name)
result={'status':'passed','official_metadata_url':url,'release_url':metadata['html_url'],
        'asset_url':asset['browser_download_url'],'official_sha256':asset['digest'],
        'archive_sha256':actual,'installed_bin_and_lib_files_compared':len(compared)}
(OUT/'toolchain-provenance.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2),flush=True)
