module
public import ZF192Support.Logic.Foundation.Axioms.Replacement.Syntax
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
theorem totalUnique_functional {Γ : Context} (ctx : EqualityContext Γ) (phi : Formula)
 (ht : ND (.seq Γ (totalUnique phi))) :
 ND (.seq Γ (functionalityFormula (rename repAIndex phi) (rename repBIndex phi))) := by
 apply ND.allI; apply ND.allI; apply ND.allI; apply ND.ii; apply ND.ii
 let G := shiftContext (shiftContext (shiftContext Γ))
 let A := rename repAIndex phi
 let B := rename repBIndex phi
 let D := B :: A :: G
 have he := ND.allE 2 (nd_weaken_head (b := B) (nd_weaken_head (b := A) (nd_shift (nd_shift (nd_shift ht)))))
 change ND (.seq D _) at he
 simp only [subst,shift,rename,rename_comp] at he
 let m := lift (substMap 2) ∘ lift (lift Nat.succ) ∘ lift (lift Nat.succ) ∘ lift (lift Nat.succ) ∘ swapBinary
 let k := lift (lift (substMap 2)) ∘ lift (lift (lift Nat.succ)) ∘ lift (lift (lift Nat.succ)) ∘ lift (lift (lift Nat.succ)) ∘ repBIndex
 let U := Formula.and (rename m phi) (.all (.imp (rename k phi) (.eq 0 1)))
 change ND (.seq D (.ex U)) at he
 apply ND.exE he
 have hu : ND (.seq (U :: shiftContext D) (.all (.imp (rename k phi) (.eq 0 1)))) :=
   ND.ce2 (ND.ctx List.mem_cons_self)
 have hy := ND.allE 2 hu
 have hz := ND.allE 1 hu
 have hma : substMap 2 ∘ k = Nat.succ ∘ repAIndex := by
   funext i; cases i with
   | zero => rfl
   | succ i => cases i <;> simp [k,repBIndex,repAIndex,lift,substMap,Function.comp_def,Nat.add_assoc]
 have hmb : substMap 1 ∘ k = Nat.succ ∘ repBIndex := by
   funext i; cases i with
   | zero => rfl
   | succ i => cases i <;> simp [k,repBIndex,lift,substMap,Function.comp_def,Nat.add_assoc]
 have hya : ND (.seq (U :: shiftContext D) (.imp (shift A) (.eq 2 0))) := by
   simpa only [subst,rename,rename_comp,hma,shift,A,lift,substMap] using hy
 have hzb : ND (.seq (U :: shiftContext D) (.imp (shift B) (.eq 1 0))) := by
   simpa only [subst,rename,rename_comp,hmb,shift,B,lift,substMap] using hz
 have ha : ND (.seq (U :: shiftContext D) (shift A)) := ND.ctx (by simp [D,shiftContext])
 have hb : ND (.seq (U :: shiftContext D) (shift B)) := ND.ctx (by simp [D,shiftContext])
 have hc : EqualityContext (U :: shiftContext D) :=
   ((ctx.shift.shift.shift.cons A).cons B).shift.cons U
 exact eq_trans hc (ND.ie hya ha) (eq_symm hc (ND.ie hzb hb))

end ZFR.FoundationBridge
