#!/usr/bin/env python3
"""Wrap already checked runtime certificates in exact census-indexed types.
No new execution obligations are claimed by these wrappers.
"""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parents[1];shard=int(sys.argv[1]);assert 16<=shard<=40
source=json.loads((root/f'data/shard{shard:03}_manifest.json').read_text())
parts=source['parts'];out=[]
def save(p,s):
 f=root/p;f.parent.mkdir(parents=True,exist_ok=True)
 if f.exists():assert f.read_text()==s, f'Refusing differing output {p}'
 else:f.write_text(s)
for part,entry in enumerate(parts):
 ks=entry['indices'];src=f'PA215.ContractShards.Shard{shard:03}Part{part}';ns=f'PA215.IndexedContracts.Shard{shard:03}Part{part}'
 s=f'import PA215.OriginalRegistry\nimport PA215.OriginalSelectors\nimport {src}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\nnamespace {ns}\nopen PA215.Census\nattribute [local irreducible] originalAt\n\n'
 for k in ks:
  if shard:
   binding=f'''    have h : originalAt ⟨{k}, by decide⟩ = {src}.original{k} :=
      originalAt_C{k//128:03} ⟨{k%128}, by decide⟩
    rw [h]
    exact {src}.binding{k}'''
  else:
   binding=f'''    have h : originalAt ⟨{k}, by decide⟩ = C{k//128:03}.records[{k%128}]'(by decide) :=
      originalAt_C{k//128:03} ⟨{k%128}, by decide⟩
    rw [h]
    rfl'''
  s+=f'''def indexed{k} : OriginalCertified ⟨{k}, by decide⟩ :=
  OriginalCertified.ofContract _ {src}.c{k} 4000 (by
{binding}) {src}.checked{k}
\n'''
 s+='def records : OriginalRegistry := [\n'+',\n'.join(f'  ⟨⟨{k}, by decide⟩, indexed{k}⟩' for k in ks)+']\n\n'
 s+='theorem exact_ids : records.map (fun e => e.1.val) = '+str(ks)+' := rfl\n\nend '+ns+'\n'
 p=f'PA215/IndexedContracts/Shard{shard:03}Part{part}.lean';save(p,s);out.append({'path':p,'module':ns,'indices':ks,'sha256':hashlib.sha256(s.encode()).hexdigest()})
ns=f'PA215.IndexedContracts.Shard{shard:03}'
s=''.join('import '+p['module']+'\n' for p in out)+f'namespace {ns}\nopen PA215.Census\ndef records : OriginalRegistry :=\n  '+' ++\n  '.join(p['module']+'.records' for p in out)+'\n\ntheorem exact_ids : records.map (fun e => e.1.val) = '+str(source['indices'])+' := by\n  simp only [records, List.map_append, '+', '.join(p['module']+'.exact_ids' for p in out)+']\n  all_goals rfl\n\nend '+ns+'\n'
p=f'PA215/IndexedContracts/Shard{shard:03}.lean';save(p,s)
save(f'data/indexed_shard{shard:03}_manifest.json',json.dumps({'status':'Generated indexed wrappers; compile and review are separate; adds no execution coverage','runtime_manifest_sha256':hashlib.sha256((root/f'data/shard{shard:03}_manifest.json').read_bytes()).hexdigest(),'indices':source['indices'],'parts':out,'aggregator':{'path':p,'sha256':hashlib.sha256(s.encode()).hexdigest()}},indent=2)+'\n')
print(f'Generated indexed wrappers for shard{shard:03}: {len(source["indices"])} IDs (no new execution coverage).')
