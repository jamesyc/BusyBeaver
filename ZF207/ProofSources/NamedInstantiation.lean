module
public import AtomicTranslation
@[expose] public section
namespace ZFR
open C207Soundness

def replaceName (i t : Nat) (ρ : Nat → Nat) (j : Nat) := if j = i then t else ρ j

theorem subst_translate_bind (i t : Nat) (ρ : Nat → Nat) (p : C207Soundness.Formula) :
    subst t (translate (bindName i ρ) p) = translate (replaceName i t ρ) p := by
  unfold subst
  rw [rename_translate]
  congr 1
  funext j
  by_cases h : j = i <;> simp [bindName,replaceName,h,substMap]

theorem subst_translateCode_bind (i t : Nat) (ρ : Nat → Nat) (n : Nat) :
    subst t (translateCode (bindName i ρ) n) = translateCode (replaceName i t ρ) n :=
  subst_translate_bind i t ρ (decodeNat n)
end ZFR
