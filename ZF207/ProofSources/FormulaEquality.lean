module
public import FoundationTemplate
public import QuantifierTemplates
@[expose] public section
namespace ZFR

def zfrTrans : Formula := .all (.all (.all (.imp (.eq 2 1) (.imp (.eq 1 0) (.eq 2 0)))))
@[simp] theorem shift_zfrTrans : shift zfrTrans = zfrTrans := rfl

structure EqualityContext (Γ : Context) : Prop where
 refl : zfrRefl ∈ Γ
 sym : zfrSym ∈ Γ
 trans : zfrTrans ∈ Γ
 elem : zfrEqElem ∈ Γ

theorem EqualityContext.cons {Γ : Context} (h : EqualityContext Γ) (p : Formula) : EqualityContext (p::Γ) :=
 ⟨by simp [h.refl],by simp [h.sym],by simp [h.trans],by simp [h.elem]⟩
theorem EqualityContext.shift {Γ : Context} (h : EqualityContext Γ) : EqualityContext (shiftContext Γ) :=
 ⟨shifted_member h.refl shift_zfrRefl,shifted_member h.sym shift_zfrSym,
 shifted_member h.trans shift_zfrTrans,shifted_member h.elem shift_zfrEqElem⟩

theorem nd_trans_instance {Γ : Context} (h : zfrTrans ∈ Γ) (a b c : Nat) :
 ND (.seq Γ (.imp (.eq a b) (.imp (.eq b c) (.eq a c)))) := by
 have ht := ND.allE c (ND.allE b (ND.allE a (ND.ctx h)))
 simpa [zfrTrans,subst,rename,lift,substMap] using ht

theorem eq_symm {Γ : Context} (ctx : EqualityContext Γ) {i j : Nat}
 (h : ND (.seq Γ (.eq i j))) : ND (.seq Γ (.eq j i)) := ND.ie (nd_sym_instance ctx.sym i j) h

theorem eq_trans {Γ : Context} (ctx : EqualityContext Γ) {i j k : Nat}
 (h : ND (.seq Γ (.eq i j))) (g : ND (.seq Γ (.eq j k))) : ND (.seq Γ (.eq i k)) :=
 ND.ie (ND.ie (nd_trans_instance ctx.trans i j k) h) g

end ZFR
