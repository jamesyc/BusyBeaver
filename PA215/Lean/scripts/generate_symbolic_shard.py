#!/usr/bin/env python3
"""Generate one bounded continuation shard (1..40), never execution/search output.

Each record is selected from the exact typed original census, and every accepted
entry carries a kernel proof of both original binding and checker success.
"""
from pathlib import Path
import gzip,hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1]
shard=int(sys.argv[1]);assert 1<=shard<=40
with gzip.open(ROOT/'data/original_contracts.json.gz','rb') as f:raw=f.read(16037505)
SHA='7cc47482b8ffcaad47dac92c9033a54a93d1a43d4686db2ccd165542897dfffe'
assert len(raw)==16037504 and hashlib.sha256(raw).hexdigest()==SHA
cs=json.loads(raw)
base={0,1,2,5,6,7,4942,5084,5085,5086,5087,5088,5114}
first=[k for k in range(5134) if k not in base][:128]
remaining=[k for k in range(5134) if k not in base and k not in set(first)]
assert len(remaining)==4993
ids=remaining[(shard-1)*128:shard*128];assert 1<=len(ids)<=128

def save(path,s):
    p=ROOT/path;p.parent.mkdir(parents=True,exist_ok=True)
    if p.exists():assert p.read_text()==s,f'Refusing differing output: {p}'
    else:p.write_text(s)
mods=[]
for part in range((len(ids)+15)//16):
    ks=ids[part*16:part*16+16];ns=f'Shard{shard:03}Part{part}'
    needed=sorted({k//128 for k in ks})
    s='import PA215.CertifiedContracts\n'+''.join(f'import PA215.Census.C{i:03}\n' for i in needed)+'set_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\n\nnamespace PA215.ContractShards.'+ns+'\nopen PA215.Contracts PA215.Census\n\n'
    for k in ks:
        assert cs[k]['index']==k and not cs[k]['halt']
        s+=f'''def original{k} : RawOriginal := C{k//128:03}.records[{k%128}]'(by decide)
theorem original_id{k} : original{k}.index = {k} := by decide

def c{k} : Contract := original{k}.toContract.get (by decide)
theorem binding{k} : original{k}.toContract = some c{k} := rfl

theorem checked{k} : check 4000 c{k} = true := by decide

'''
    s+='def records : List Certified := [\n'+',\n'.join(f'  ⟨{k}, c{k}, 4000, checked{k}⟩' for k in ks)+']\n\nend PA215.ContractShards.'+ns+'\n'
    path=f'PA215/ContractShards/{ns}.lean';save(path,s);mods.append({'module':'PA215.ContractShards.'+ns,'path':path,'indices':ks,'sha256':hashlib.sha256(s.encode()).hexdigest()})
s=''.join('import '+m['module']+'\n' for m in mods)+'set_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\n\nnamespace PA215.ContractShards.Shard'+f'{shard:03}'+'\nopen PA215.Contracts\n\ndef records : List Certified :=\n  '+' ++\n  '.join(f'PA215.ContractShards.Shard{shard:03}Part{i}.records' for i in range(len(mods)))+'\n\ndef ids : List Nat := records.map Certified.id\n\n'
s+=f'theorem exact_ids : ids = {ids} := by decide\ntheorem count : records.length = {len(ids)} := by decide\ntheorem distinct_ids : ids.Nodup := by decide\n\nend PA215.ContractShards.Shard{shard:03}\n'
path=f'PA215/ContractShards/Shard{shard:03}.lean';save(path,s)
man={'source_corpus_sha256':SHA,'shard':shard,'indices':ids,'parts':mods,'aggregator':{'path':path,'sha256':hashlib.sha256(s.encode()).hexdigest()},'status':'Generated obligations; kernel build/review/publication are separate.'}
save(f'data/shard{shard:03}_manifest.json',json.dumps(man,indent=2)+'\n')
print(f'Generated/revalidated shard{shard:03}: {len(ids)} new original IDs, from{ids[0]} through{ids[-1]}.')
