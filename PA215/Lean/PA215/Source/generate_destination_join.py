#!/usr/bin/env python3
"""Untrusted cached proof generator. Every lookup/resolve/plan is kernel checked."""
import json,gzip,hashlib,pathlib,sys
source,census,out,first,last=sys.argv[1:]
source=pathlib.Path(source);census=pathlib.Path(census);out=pathlib.Path(out)
assert hashlib.sha256(source.read_bytes()).hexdigest()=='e4814e0d968b86a8cd4cf2df2623b2f5558a7a61bf43b99f798c73156eb91c45'
assert hashlib.sha256(census.read_bytes()).hexdigest()=='4dd3e8b97540fe0420de80db200ba4e13dc3bf98e63a159b44fb1afae6769245'
sites=json.loads(source.read_bytes());rs=json.loads(gzip.decompress(census.read_bytes()))
physical=[6,2,0,4,3,7,8,5,1]
def path(p):return '['+','.join('true' if b=='1' else 'false'for b in p)+']'
def succ(p):
 if '0' not in p:return None
 i=p.rindex('0');return p[:i]+'1'+'0'*(len(p)-i-1)
def cut(p,b,n):
 for _ in range(n):p=p[:p.rindex(b)]
 return p
def locate(p):
 return next(i for i,(s,_) in enumerate(sites)if s.startswith(p) or(p.startswith(s)and set(p[len(s):])<=set('0')))
def after(p):
 q=succ(p);return None if q is None else locate(q)
def opt(n):return 'none'if n is None else f'(some {n})'
def instruction(idx):
 p,(tag,arg)=sites[idx]
 if tag=='EInc':return f'.inc {arg} {opt(after(p))}'
 if tag=='EDecnz':return f'.dec {arg} {opt(after(cut(p,"0",1)))} {opt(after(p))}'
 if tag=='EBreak':return f'.jump {opt(after(cut(p,"0",arg)))}'
 if tag=='EContinue':return f'.jump (some {locate(cut(p,"1",arg))})'
 return '.halt'
def result(r):
 p,(tag,arg)=sites[r['site_index']];extra=0;e='.none'
 if tag=='EHalt':return None
 if tag=='EContinue':q=cut(p,'1',arg);return q,0,e,locate(q),False
 if tag=='EInc':e=f'(.inc {physical[arg]})'
 if tag=='EDecnz':
  if r['branch'][1]:p=cut(p,'0',1)
  else:extra=1;e=f'(.dec {physical[arg]})'
 if tag=='EBreak':p=cut(p,'0',arg)
 q=succ(p)
 if q is None:return '',extra+1,e,0,True
 return q,extra,e,locate(q),False
out.mkdir(parents=True,exist_ok=True)
for batch in range(int(first),int(last)+1):
 k=f'{batch:03d}';records=rs[128*batch:128*(batch+1)];curr={r['site_index']for r in records};allidx=curr|{result(r)[3]for r in records if result(r)is not None}
 s=f'import PA215.Source.DestinationCertificate\nimport PA215.Census.C{k}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 16000000\nnamespace PA215.Source.DestinationJoin.D{k}\n'
 for i in sorted(allidx):
  p,(tag,arg)=sites[i];op={'EInc':'inc','EDecnz':'dec','EBreak':'breakTo','EContinue':'continueTo','EHalt':'halt'}[tag];op='.'+op+(' '+str(arg)if arg is not None else'')
  s+=f'private def site{i} : Site := ⟨{path(p)},{op}⟩\nprivate theorem lookup{i} : exactSites[{i}]? = some site{i} := by rfl\n'
 for i in sorted(curr):
  s+=f'private def inst{i} : Instruction := {instruction(i)}\nprivate theorem resolved{i} : resolveAt exactSites {i} = some inst{i} := by\n  rw [← PathTrie.fastResolveAt_eq]\n  unfold PathTrie.fastResolveAt\n  rw [lookup{i}]\n  rfl\n'
 for j,r in enumerate(records):
  i=r['site_index'];res=result(r)
  s+=f'private def raw{j} := PA215.Census.C{k}.records[{j}]\nprivate theorem row{j} : destinationAgrees raw{j} = true := by\n'
  if res is None:
   s+=f'  apply destination_terminal (s := site{i}) (i := inst{i})\n'
  else:
   p,extra,e,n,ex=res;q='.exited'if ex else f'(.at {n})'
   s+=f'  apply destination_nonterminal (s := site{i}) (i := inst{i})\n    (p := ⟨{path(p)},{extra},{e}⟩) (q := {q}) (e := {e}) (k := {n}) (next := site{n})\n'
  s+=f'  · rw [show raw{j}.siteIndex = {i} from rfl]\n    exact lookup{i}\n  · rw [show raw{j}.siteIndex = {i} from rfl]\n    exact resolved{i}\n  · decide\n  · decide\n'
  if res is not None:s+=f'  · rfl\n  · exact lookup{n}\n  · decide\n'
 s+=f'private theorem enumeration : PA215.Census.C{k}.records.toList = ['+','.join(f'raw{j}'for j in range(len(records)))+'] := by rfl\n'
 s+=f'theorem checked : PA215.Census.C{k}.records.toList.all destinationAgrees = true := by\n  rw [enumeration]\n  simp only [List.all_cons,List.all_nil,'+','.join(f'row{j}'for j in range(len(records)))+f',Bool.and_self]\n#print axioms checked\nend PA215.Source.DestinationJoin.D{k}\n'
 (out/f'D{k}.lean').write_text(s)
