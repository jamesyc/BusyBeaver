#!/usr/bin/env python3
"""Independent parser audit for bounded128-shard literals and registry IDs.

This does not invoke the generator and is not a substitute for kernel checking.
"""
from pathlib import Path
import gzip, hashlib, json, re
ROOT=Path(__file__).resolve().parents[1]
with gzip.open(ROOT/'data/original_contracts.json.gz','rb') as f: raw=f.read(16037505)
assert len(raw)==16037504 and hashlib.sha256(raw).hexdigest()=='7cc47482b8ffcaad47dac92c9033a54a93d1a43d4686db2ccd165542897dfffe'
corpus=json.loads(raw)
m=json.loads((ROOT/'data/shard000_manifest.json').read_text())
expected=[k for k in range(5134) if k not in {0,1,2,5,6,7,4942,5084,5085,5086,5087,5088,5114}][:128]
assert m['indices']==expected and len(set(expected))==128
class Parser:
    def __init__(self,s):
        pat=r'\.[A-Za-z]+|[A-Za-z]+|\d+|[⟨⟩(),\[\]]'
        self.ts=re.findall(pat,s); self.pos=0
        assert not re.sub(pat,'',s).strip()
    def take(self,w=None):
        t=self.ts[self.pos];self.pos+=1
        if w is not None:assert t==w,(t,w)
        return t
    def boolean(self):
        x=self.take();assert x in ('true','false');return x=='true'
    def nat(self):return int(self.take())
    def branch(self):
        x=self.take()
        if x=='none':return None
        assert x=='some';self.take('(');n=self.nat();self.take(',');b=self.boolean();self.take(')');return[n,b]
    def seg(self):
        x=self.take()
        if x=='.run':return['r',int(self.boolean()),self.nat(),self.nat()]
        assert x=='.box';self.take('(');kind=self.take()
        if kind=='.mark':v=['b','mark',self.nat()]
        else:
            assert kind=='.plain';kind=self.take()
            if kind=='.none':v=['b','none',-1]
            else:
                assert kind=='(';op=self.take();assert op in ('.inc','.dec')
                v=['b',op[1:],self.nat()];self.take(')')
        self.take(')');return v
    def segs(self):
        self.take('[');r=[]
        if self.ts[self.pos]!=']':
            while True:
                r.append(self.seg())
                if self.ts[self.pos]!=',':break
                self.take(',')
        self.take(']');return r
    def state(self):
        self.take('(');q=str(self.nat());self.take(',');on=self.boolean();self.take(',');left=self.segs();self.take(',');right=self.segs();self.take(')')
        return dict(q=q,on_left=on,left=left,right=right)
    def contract(self):
        self.take('⟨');br=self.branch();self.take(',');a=self.state();self.take(',');b=self.state();self.take('⟩');assert self.pos==len(self.ts)
        return dict(branch=br,initial=a,target=b)
seen=[]
for part in m['parts']:
    path=ROOT/part['path'];data=path.read_bytes();assert hashlib.sha256(data).hexdigest()==part['sha256']
    text=data.decode();defs=re.findall(r'^def c(\d+) : Contract := (.+)$',text,re.M)
    ids=[int(k) for k,_ in defs];assert ids==part['indices']
    for k,s in defs:
        k=int(k);got=Parser(s).contract();orig=corpus[k]
        assert not orig['halt'] and got=={key:orig[key] for key in got},k
        assert re.search(rf'theorem checked{k} : check 4000 c{k} = true := by decide\b',text)
    regs=re.findall(r'⟨(\d+), c(\d+), 4000, checked(\d+)⟩',text)
    assert regs==[(str(k),str(k),str(k)) for k in ids]
    seen+=ids
assert seen==expected
agg=(ROOT/m['aggregator']['path']).read_bytes();assert hashlib.sha256(agg).hexdigest()==m['aggregator']['sha256']
assert agg.decode().count('import PA215.ContractShards.Shard000Part')==8
print('PASS:128 distinct original initial/target/branch inputs and certified registry IDs; no prior-ID overlap.')
