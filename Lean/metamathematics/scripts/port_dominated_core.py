#!/usr/bin/env python3
"""Untrusted syntax-only Coq→Lean proof-term port; Lean checks every emitted term."""
import hashlib,re,sys
from pathlib import Path
source_bytes=Path(sys.argv[1]).read_bytes()
assert hashlib.sha256(source_bytes).hexdigest() == 'ce27f2836c3723763964738fc7dfb07ae42ae90028a6564cbccb45466f2b73fe', 'Unexpected DominatedCore.v source bytes'
source=source_bytes.decode('utf-8')
pat=r'^(?:Lemma|Theorem)\s+(\w+)\s+(.+?)\.\nProof\. exact (.+?)\. Qed\.'
matches=list(re.finditer(pat,source,re.M|re.S))
assert len(matches)==62
assert [m[1] for m in matches[-6:]]==['rho8_all','composition','lift_right','k','peirce','s']
def tr(x):
 x=re.sub(r'\bimp\b','wim',x)
 x=re.sub(r'\bT\b','Derivation',x)
 return re.sub(r'below (\w+) (\w+)',r'\1 ≤ \2',x)
out='''import PA215PA.NativeDecode

/-! Finite dominated-rho8 replacement, ported term-for-term from DominatedCore.v
at VladimirReshetnikov/ProveIt@6809609c61b9f2dd11c66374952cc5eb3defbd9f.
Only its generic propositional proof is reused, not a ZFC machine or endpoint.
Every row has an actual Nat inequality proof; every MP constructs the real
finite dominated native derivation. No unrestricted row is assumed. -/
namespace PA215.PA.NativeCalculus.Dominated
set_option autoImplicit false

private abbrev below := Nat.le

private def mp (a b : Nat) (major : Derivation (wim a b)) (minor : Derivation a) :
    Derivation b := .mp minor major
private def row (a b c u : Nat) (h : u ≤ a) : Derivation (rho8 a b c u) :=
  .r8 a b c u h
private theorem refl (a : Nat) : a ≤ a := Nat.le_refl a
private theorem le_l {u x : Nat} (y : Nat) (h : u ≤ x) : u ≤ wim x y := by
  have hp := NumericDecode.pair_bounds x y
  simp only [wim,PA215.Source.Cantor.implication]
  omega
private theorem le_r {u y : Nat} (x : Nat) (h : u ≤ y) : u ≤ wim x y := by
  have hp := NumericDecode.pair_bounds x y
  simp only [wim,PA215.Source.Cantor.implication]
  omega

'''
for m in matches:
 name,signature,body=m.groups()
 depth=0
 for pos,char in enumerate(signature):
  if char=='(' : depth+=1
  elif char==')': depth-=1
  elif char==':' and depth==0: break
 else: raise ValueError('missing result colon '+name)
 header=signature[:pos].strip();target=signature[pos+1:].strip()
 assert target.startswith('T '), (name,target)
 target=target[2:];parts=[];i=0
 while i<len(header):
  if header[i].isspace():i+=1;continue
  if header[i]=='(':
   j=i+1;depth=1
   while depth:
    depth+=(header[j]=='(')-(header[j]==')');j+=1
   parts.append(tr(header[i:j]));i=j
  else:
   j=i
   while j<len(header) and not header[j].isspace() and header[j]!='(':j+=1
   parts.append('('+header[i:j]+' : Nat)');i=j
 out+=('private ' if name.startswith('d') and name[1:].isdigit() else '')+'def '+name+' '+' '.join(parts)+' :\n  Derivation '+tr(target)+' :=\n  '+tr(body)+'\n\n'
out+='''#print axioms rho8_all
#print axioms composition
#print axioms k
#print axioms peirce
#print axioms s
end PA215.PA.NativeCalculus.Dominated
'''
Path(sys.argv[2]).write_text(out)
print(f'Emitted {len(matches)} proof terms; not checked until Lean succeeds.')
