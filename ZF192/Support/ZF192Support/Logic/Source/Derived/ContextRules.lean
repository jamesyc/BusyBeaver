module
public import ZF192Support.Logic.Source.Derived.EqualityInstances
@[expose] public section
namespace ZFR

def zfrSym : Formula := .all (.all (.imp (.eq 1 0) (.eq 0 1)))
@[simp] theorem shift_zfrRefl : shift zfrRefl = zfrRefl := rfl
@[simp] theorem shift_zfrEqElem : shift zfrEqElem = zfrEqElem := rfl
@[simp] theorem shift_zfrSym : shift zfrSym = zfrSym := rfl

theorem shifted_member {a : Formula} {Γ : Context} (ha : a ∈ Γ) (h : shift a = a) : a ∈ shiftContext Γ := by
 exact List.mem_map.mpr ⟨a,ha,h⟩

theorem nd_sym_instance {Γ : Context} (h : zfrSym ∈ Γ) (a b : Nat) :
 ND (.seq Γ (.imp (.eq a b) (.eq b a))) := by
 have ht := ND.allE b (ND.allE a (ND.ctx h))
 simpa [zfrSym, subst, rename, lift, substMap] using ht

theorem nd_weaken_head {Γ : Context} {a b : Formula} (h : ND (.seq Γ a)) : ND (.seq (b::Γ) a) :=
 ND.wk (by intro x hx; simp [hx]) h

theorem nd_shift {Γ : Context} {a : Formula} (h : ND (.seq Γ a)) :
 ND (.seq (shiftContext Γ) (shift a)) := h.rename Nat.succ

end ZFR
