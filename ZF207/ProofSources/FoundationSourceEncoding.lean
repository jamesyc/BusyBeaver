module
public import FoundationNegationBridge
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

theorem toSource_ofSource_equiv (p : ZFR.Formula) (n : Nat) (Γ : Context) :
 NDEquiv Γ (toSource (ofSource n p)) p := by
 induction p generalizing n Γ with
 | bot => exact NDEquiv.refl _ _
 | mem i j => simp only [ofSource,toSource,atom,Matrix.cons_val_zero,Matrix.cons_val_one,termIndex_sourceTerm]; exact NDEquiv.refl _ _
 | eq i j => simp only [ofSource,toSource,atom,Matrix.cons_val_zero,Matrix.cons_val_one,termIndex_sourceTerm]; exact NDEquiv.refl _ _
 | and p q ihp ihq => exact NDEquiv.and (ihp n Γ) (ihq n Γ)
 | or p q ihp ihq => exact or_equiv (ihp n Γ) (ihq n Γ)
 | imp p q ihp ihq =>
   exact (toSource_arrow_equiv Γ (ofSource n p) (ofSource n q)).trans (NDEquiv.imp (ihp n Γ) (ihq n Γ))
 | all p ih => exact NDEquiv.all (ih (n+1) (shiftContext Γ))
 | ex p ih => exact NDEquiv.ex (ih (n+1) (shiftContext Γ))

end ZFR.FoundationBridge
