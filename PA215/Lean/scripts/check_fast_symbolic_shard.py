#!/usr/bin/env python3
"""Independent bounded-shard audit of original selectors and proof registry IDs."""
from pathlib import Path
import hashlib,json,re,sys
ROOT=Path(__file__).resolve().parents[1];shard=int(sys.argv[1]);assert 16<=shard<=40
m=json.loads((ROOT/f'data/shard{shard:03}_manifest.json').read_text())
assert m['proof_method']=='verified_flat_lookup'
assert m['lookup_equivalence_sha256']=='a3316b7effdbccf1040ad4a7a9f2b55c78b08aa76ca1b8e570c71fdac514d286'
assert m['lookup_equivalence_sha256']==hashlib.sha256((ROOT/'PA215/FastNativeTable.lean').read_bytes()).hexdigest()
# Independently spell out the paid domain; do not call the generator.
paid={0,1,2,5,6,7,4942,5084,5085,5086,5087,5088,5114}|{3,4}|set(range(8,134))
remaining=[i for i in range(5134) if i not in paid]
ids=remaining[(shard-1)*128:shard*128];assert m['indices']==ids and len(set(ids))==len(ids)
cm=json.loads((ROOT/'data/original_census_manifest.json').read_text())
assert cm['source_corpus_sha256']==m['source_corpus_sha256']=='7cc47482b8ffcaad47dac92c9033a54a93d1a43d4686db2ccd165542897dfffe'
assert (ROOT/'PA215/FastNativeTable.lean').is_file()
seen=[]
for part in m['parts']:
    raw=(ROOT/part['path']).read_bytes();assert hashlib.sha256(raw).hexdigest()==part['sha256'];s=raw.decode()
    originals=re.findall(r"def original(\d+) : RawOriginal := C(\d+)\.records\[(\d+)\]'\(by decide\)",s)
    ks=[int(x[0]) for x in originals];assert ks==part['indices']
    for k,a,b in originals:
        k,a,b=map(int,(k,a,b));assert a*128+b==k and 0<=b<128
        cp=cm['parts'][a];assert cp['lo']<=k<cp['lo']+cp['count']
        assert hashlib.sha256((ROOT/cp['path']).read_bytes()).hexdigest()==cp['sha256']
        assert f'def c{k} : Contract := original{k}.toContract.get (by decide)' in s
        assert f'theorem binding{k} : original{k}.toContract = some c{k} := rfl' in s
        assert f'theorem checked{k} : check 4000 c{k} = true := by\n  rw [← PA215.FastNativeTable.fastCheck_eq_check]\n  decide' in s
    regs=re.findall(r'⟨(\d+), c(\d+), 4000, checked(\d+)⟩',s)
    assert regs==[(str(k),str(k),str(k)) for k in ks];seen+=ks
assert seen==ids
agg=(ROOT/m['aggregator']['path']).read_bytes();assert hashlib.sha256(agg).hexdigest()==m['aggregator']['sha256']
assert len(re.findall(r'^import PA215\.ContractShards\.Shard\d+Part\d+$',agg.decode(),re.M))==len(m['parts'])
print(f'PASS: shard{shard:03}, {len(ids)} original selectors, explicit bindings and registry IDs; no paid-ID overlap.')
