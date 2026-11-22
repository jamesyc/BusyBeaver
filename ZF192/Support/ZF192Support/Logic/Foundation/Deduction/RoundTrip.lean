module
public import ZF192Support.Logic.Foundation.Syntax.FromSource
public import ZF192Support.Logic.Foundation.Deduction.Negation
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder

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
