#!/usr/bin/env python3
"""Independent literal/statement census audit; Lean remains the proof authority.
Usage: check_cached_source_join_v2.py SOURCE.json REPOSITORY
"""
from pathlib import Path
import gzip, hashlib, json, re, sys
source_path, root = map(Path, sys.argv[1:])
assert hashlib.sha256(source_path.read_bytes()).hexdigest() == 'e4814e0d968b86a8cd4cf2df2623b2f5558a7a61bf43b99f798c73156eb91c45'
source = json.loads(source_path.read_text())
raw = root / 'data/original_contracts.json.gz'
assert hashlib.sha256(raw.read_bytes()).hexdigest() == '4dd3e8b97540fe0420de80db200ba4e13dc3bf98e63a159b44fb1afae6769245'
records = json.loads(gzip.decompress(raw.read_bytes()))
ops = {'EInc':'inc','EDecnz':'dec','EBreak':'breakTo','EContinue':'continueTo','EHalt':'halt'}
report = {}
for chunk in range(26,32):
    name = f'J{chunk:03}'
    p = root / f'PA215/Source/CensusJoinCachedV2/{name}.lean'
    old = root / f'PA215/Source/CensusJoin/{name}.lean'
    text = p.read_text()
    expected = f'PA215.Census.C{chunk:03}.records.toList.all recordAgrees = true'
    for content in (text,old.read_text()):
        assert re.search(r'theorem checked : (.*?) := by',content).group(1) == expected
    rs = records[128*chunk:128*(chunk+1)]
    sites = {int(i):(path,op,arg) for i,path,op,arg in re.findall(r'private def site(\d+) : Site := ⟨\[(.*?)\],\.(\w+)(?: (\d+))?⟩',text)}
    assert set(sites) == {r['site_index'] for r in rs}
    for index,(path,op,arg) in sites.items():
        input_path,(tag,input_arg) = source[index]
        decoded = ''.join({'true':'1','false':'0'}[b] for b in path.split(',') if b)
        assert decoded == input_path and op == ops[tag]
        assert (int(arg) if arg else None) == input_arg
        assert f'private theorem lookup{index} : exactSites[{index}]? = some site{index} := by rfl' in text
    for i,r in enumerate(rs):
        assert f"private def raw{i} := PA215.Census.C{chunk:03}.records[{i}]'(by decide)" in text
        index = r['site_index']
        body = f'private theorem row{i} : recordAgrees raw{i} = true := by\n  unfold recordAgrees\n  rw [show raw{i}.siteIndex = {index} from rfl,lookup{index}]\n  decide'
        assert body in text
    enum = ','.join(f'raw{i}' for i in range(len(rs)))
    assert f'private theorem enumeration : PA215.Census.C{chunk:03}.records.toList = [{enum}] := by rfl' in text
    assert re.findall(r'private theorem row(\d+) :',text) == list(map(str,range(128)))
    assert f'namespace PA215.Source.CensusJoinCachedV2.{name}' in text
    assert 'import PA215.Source.AllContractFrames' not in text
    report[name] = {'rows':len(rs),'sites':len(sites),'statement':expected,
       'old_sha256':hashlib.sha256(old.read_bytes()).hexdigest(),
       'new_sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
print(json.dumps(report,indent=2))
