#!/usr/bin/env python3
"""Reproduce original5134 typed INPUT records, not execution proofs.

Pins complete original corpus. Existing differing files are never overwritten.
"""
from pathlib import Path
import gzip, hashlib, json
ROOT=Path(__file__).resolve().parents[1]
with gzip.open(ROOT/'data/original_contracts.json.gz','rb') as f:raw=f.read(16037505)
SHA='7cc47482b8ffcaad47dac92c9033a54a93d1a43d4686db2ccd165542897dfffe'
assert len(raw)==16037504 and hashlib.sha256(raw).hexdigest()==SHA
cs=json.loads(raw);assert len(cs)==5134 and [c['index'] for c in cs]==list(range(5134))
def seg(x):
    if x[0]=='r':return f'.run {str(bool(x[1])).lower()} {x[2]} {x[3]}'
    assert x[0]=='b'
    if x[1]=='none':assert x[2]==-1;return '.box (.plain .none)'
    if x[1] in ('inc','dec'):return f'.box (.plain (.{x[1]} {x[2]}))'
    assert x[1]=='mark';return f'.box (.mark {x[2]})'
def state(x):return f'({x["q"]}, {str(x["on_left"]).lower()}, ['+', '.join(map(seg,x['left']))+'], ['+', '.join(map(seg,x['right']))+'])'
def original(c):
    br='none' if c['branch'] is None else f'some ({c["branch"][0]}, {str(c["branch"][1]).lower()})'
    arg='none' if c['arg'] is None else f'some {c["arg"]}'
    target='none' if c['target'] is None else 'some '+state(c['target'])
    path='['+', '.join('true' if b=='1' else 'false' for b in c['path'])+']'
    return f'⟨{c["index"]}, {c["site_index"]}, {path}, "{c["tag"]}", {arg}, {br}, {state(c["initial"])}, {target}, {str(c["halt"]).lower()}⟩'
def save(path,s):
    p=ROOT/path;p.parent.mkdir(parents=True,exist_ok=True)
    if p.exists():assert p.read_text()==s, f'Refusing differing output: {p}'
    else:p.write_text(s)
mods=[]
for part,lo in enumerate(range(0,5134,128)):
    rows=cs[lo:lo+128];ns=f'C{part:03}'
    s='import PA215.OriginalCensusTypes\nset_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\n\nnamespace PA215.Census.'+ns+'\nopen PA215.Runtime\n\ndef records : Array RawOriginal := #[\n'+',\n'.join('  '+original(c) for c in rows)+']\n\n'
    s+=f'theorem size : records.size = {len(rows)} := by decide\n\ntheorem indices : records.toList.map RawOriginal.index = List.range\' {lo} {len(rows)} := by decide\n\nend PA215.Census.{ns}\n'
    path=f'PA215/Census/{ns}.lean';save(path,s);mods.append({'module':'PA215.Census.'+ns,'path':path,'lo':lo,'count':len(rows),'sha256':hashlib.sha256(s.encode()).hexdigest()})
merges='  simp only [List.append_assoc]\n'+''.join(f"  rw [show List.range' {128*i} 128 ++ List.range' {128*(i+1)} {5134-128*(i+1)} = List.range' {128*i} {5134-128*i} from List.range'_append]\n" for i in reversed(range(40)))
s=''.join('import '+m['module']+'\n' for m in mods)+'\nnamespace PA215.Census\n\ndef all : Array RawOriginal :=\n  '+' ++\n  '.join(f'C{i:03}.records' for i in range(len(mods)))+'\n\ntheorem all_size : all.size = 5134 := by\n  simp only [all, Array.size_append, '+', '.join(f'C{i:03}.size' for i in range(len(mods)))+']\n\ntheorem all_indices : all.toList.map RawOriginal.index = List.range 5134 := by\n  simp only [all, Array.toList_append, List.map_append, '+', '.join(f'C{i:03}.indices' for i in range(len(mods)))+", List.range_eq_range']\n"+merges+"\n/-- Indexing is total on the exact original5134-ID domain. -/\ndef originalAt (i : Fin 5134) : RawOriginal :=\n  all[i.val]'(by rw [all_size]; exact i.isLt)\n\nend PA215.Census\n"
path='PA215/OriginalCensus.lean';save(path,s)
man={'source_corpus_sha256':SHA,'count':5134,'parts':mods,'aggregator':{'path':path,'sha256':hashlib.sha256(s.encode()).hexdigest()},'scope':'Typed original inputs and index/size facts only. Execution certificates are separate.'}
save('data/original_census_manifest.json',json.dumps(man,indent=2)+'\n')
print('Generated/revalidated5134 original records in41 bounded input modules.')
