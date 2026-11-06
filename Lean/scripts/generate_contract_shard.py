#!/usr/bin/env python3
"""Reproduce bounded shard000 (128 new originals); generates untrusted Lean input.

Only Lean kernel acceptance proves anything. Exact input audit is independent of
success; existing output must match byte-for-byte or the script refuses overwrite.
"""
from pathlib import Path
import gzip, hashlib, json
ROOT = Path(__file__).resolve().parents[1]
with gzip.open(ROOT/'data/original_contracts.json.gz','rb') as f:
    raw=f.read(16037505)
assert len(raw)==16037504 and hashlib.sha256(raw).hexdigest()=='7cc47482b8ffcaad47dac92c9033a54a93d1a43d4686db2ccd165542897dfffe'
cs=json.loads(raw)
paid={0,1,2,5,6,7,4942,5084,5085,5086,5087,5088,5114}
ids=[k for k in range(5134) if k not in paid][:128]
assert len(ids)==128 and len(set(ids))==128 and not set(ids)&paid

def seg(x):
    if x[0]=='r': return f'.run {str(bool(x[1])).lower()} {x[2]} {x[3]}'
    assert x[0]=='b'
    if x[1]=='none': assert x[2]==-1; return '.box (.plain .none)'
    if x[1] in ('inc','dec'): return f'.box (.plain (.{x[1]} {x[2]}))'
    assert x[1]=='mark';return f'.box (.mark {x[2]})'
def state(x):
    return f'({x["q"]}, {str(x["on_left"]).lower()}, ['+', '.join(map(seg,x['left']))+'], ['+', '.join(map(seg,x['right']))+'])'
def decl(c):
    br='none' if c['branch'] is None else f'some ({c["branch"][0]}, {str(c["branch"][1]).lower()})'
    return f'⟨{br}, {state(c["initial"])}, {state(c["target"])}⟩'
def save(path,text):
    p=ROOT/path;p.parent.mkdir(parents=True,exist_ok=True)
    if p.exists(): assert p.read_text()==text, f'Refusing differing output: {p}'
    else:p.write_text(text)
mods=[]
for chunk in range(8):
    ks=ids[chunk*16:(chunk+1)*16];ns=f'Shard000Part{chunk}'
    s='import PA215.CertifiedContracts\nset_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\n\nnamespace PA215.ContractShards.'+ns+'\nopen PA215.Contracts PA215.Runtime\n\n'
    for k in ks:
        c=cs[k];assert c['index']==k and not c['halt']
        s+=f'def c{k} : Contract := {decl(c)}\n\ntheorem checked{k} : check 4000 c{k} = true := by decide\n\n'
    s+='def records : List Certified := [\n'+',\n'.join(f'  ⟨{k}, c{k}, 4000, checked{k}⟩' for k in ks)+']\n\nend PA215.ContractShards.'+ns+'\n'
    path='PA215/ContractShards/'+ns+'.lean';save(path,s);mods.append({'module':'PA215.ContractShards.'+ns,'path':path,'indices':ks,'sha256':hashlib.sha256(s.encode()).hexdigest()})
s=''.join('import '+m['module']+'\n' for m in mods)+'\nset_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\n\nnamespace PA215.ContractShards.Shard000\nopen PA215.Contracts\n\ndef records : List Certified :=\n  '+' ++\n  '.join('PA215.ContractShards.Shard000Part'+str(k)+'.records' for k in range(8))+'\n\ndef ids : List Nat := records.map Certified.id\n\ntheorem exact_ids : ids = '+str(ids)+' := by decide\ntheorem count : records.length = 128 := by decide\ntheorem distinct_ids : ids.Nodup := by decide\n\nend PA215.ContractShards.Shard000\n'
path='PA215/ContractShards/Shard000.lean';save(path,s)
man={'source_corpus_sha256':hashlib.sha256(raw).hexdigest(),'indices':ids,'excluded_previously_paid':sorted(paid),'parts':mods,'aggregator':{'path':path,'sha256':hashlib.sha256(s.encode()).hexdigest()},'status':'Generated proof obligations; build/review/publication are separate.'}
save('data/shard000_manifest.json',json.dumps(man,indent=2)+'\n')
print('Generated/revalidated128 distinct original obligations in8 bounded parts.')
