#!/usr/bin/env python3
"""Independent literal parser: all mathematical fields of all5134 original inputs.

No generator import, no native Lean evaluation, no execution-proof claim.
"""
from pathlib import Path
import gzip,hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
with gzip.open(ROOT/'data/original_contracts.json.gz','rb') as f:raw=f.read(16037505)
SHA='7cc47482b8ffcaad47dac92c9033a54a93d1a43d4686db2ccd165542897dfffe'
assert len(raw)==16037504 and hashlib.sha256(raw).hexdigest()==SHA
cs=json.loads(raw);assert len(cs)==5134
m=json.loads((ROOT/'data/original_census_manifest.json').read_text());assert m['source_corpus_sha256']==SHA and m['count']==5134
class Parser:
    def __init__(self,s):
        pat=r'"[^"\\]*"|\.[A-Za-z]+|[A-Za-z]+|\d+|[⟨⟩(),\[\]]'
        self.ts=re.findall(pat,s);self.i=0
        assert not re.sub(pat,'',s).strip()
    def take(self,w=None):
        t=self.ts[self.i];self.i+=1
        if w is not None:assert t==w,(t,w)
        return t
    def nat(self):return int(self.take())
    def boolean(self):
        t=self.take();assert t in ('true','false');return t=='true'
    def optnat(self):
        t=self.take()
        if t=='none':return None
        assert t=='some';return self.nat()
    def branch(self):
        t=self.take()
        if t=='none':return None
        assert t=='some';self.take('(');n=self.nat();self.take(',');b=self.boolean();self.take(')');return[n,b]
    def seg(self):
        t=self.take()
        if t=='.run':return['r',int(self.boolean()),self.nat(),self.nat()]
        assert t=='.box';self.take('(');t=self.take()
        if t=='.mark':r=['b','mark',self.nat()]
        else:
            assert t=='.plain';t=self.take()
            if t=='.none':r=['b','none',-1]
            else:
                assert t=='(';op=self.take();assert op in('.inc','.dec');r=['b',op[1:],self.nat()];self.take(')')
        self.take(')');return r
    def seq(self,read):
        self.take('[');r=[]
        if self.ts[self.i]!=']':
            while True:
                r.append(read())
                if self.ts[self.i]!=',':break
                self.take(',')
        self.take(']');return r
    def state(self):
        self.take('(');q=str(self.nat());self.take(',');on=self.boolean();self.take(',');l=self.seq(self.seg);self.take(',');r=self.seq(self.seg);self.take(')')
        return dict(q=q,on_left=on,left=l,right=r)
    def optstate(self):
        t=self.take()
        if t=='none':return None
        assert t=='some';return self.state()
    def original(self):
        self.take('⟨');k=self.nat();self.take(',');site=self.nat();self.take(',');path=self.seq(self.boolean);self.take(',');tag=json.loads(self.take());self.take(',');arg=self.optnat();self.take(',');br=self.branch();self.take(',');init=self.state();self.take(',');target=self.optstate();self.take(',');halt=self.boolean();self.take('⟩');assert self.i==len(self.ts)
        return dict(index=k,site_index=site,path=''.join('1' if b else '0' for b in path),tag=tag,arg=arg,branch=br,initial=init,target=target,halt=halt)
seen=[]
for part in m['parts']:
    b=(ROOT/part['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==part['sha256']
    body=b.decode().split('def records : Array RawOriginal := #[\n',1)[1].split(']\n\n',1)[0]
    lines=body.splitlines();assert len(lines)==part['count']
    for line in lines:
        got=Parser(line.strip().removesuffix(',')).original();k=got['index']
        assert got=={key:cs[k][key] for key in got},k
        assert got['halt']==(got['target'] is None)
        seen.append(k)
    assert seen[-len(lines):]==list(range(part['lo'],part['lo']+part['count']))
assert seen==list(range(5134))
a=(ROOT/m['aggregator']['path']).read_bytes();assert hashlib.sha256(a).hexdigest()==m['aggregator']['sha256']
assert a.decode().count('import PA215.Census.C')==41
print('PASS: all5134 original index/site/path/tag/optional-arg/branch/initial/target/halt fields exactly preserved.')
