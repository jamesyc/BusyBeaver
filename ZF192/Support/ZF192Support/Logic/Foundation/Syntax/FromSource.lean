module
public import ZF192Support.Logic.Foundation.Syntax.ToSource
@[expose] public section
namespace ZFR.FoundationBridge
open FFL.FirstOrder

def sourceTerm (n i : Nat) : Semiterm Language.set Nat n :=
 if h : i < n then .bvar ⟨i,h⟩ else .fvar (i-n)

theorem termIndex_sourceTerm (n i : Nat) : termIndex (sourceTerm n i) = i := by
 unfold sourceTerm
 split
 · rfl
 · simp only [termIndex]
   omega

def ofSource (n : Nat) : ZFR.Formula → Semiformula Language.set Nat n
 | .bot => .falsum
 | .mem i j => .rel .mem ![sourceTerm n i,sourceTerm n j]
 | .eq i j => .rel .eq ![sourceTerm n i,sourceTerm n j]
 | .and p q => .and (ofSource n p) (ofSource n q)
 | .or p q => .or (ofSource n p) (ofSource n q)
 | .imp p q => .or (Semiformula.neg (ofSource n p)) (ofSource n q)
 | .all p => .all (ofSource (n+1) p)
 | .ex p => .exs (ofSource (n+1) p)

end ZFR.FoundationBridge
