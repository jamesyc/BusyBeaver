module
public import Internal.Tait.Rename
@[expose] public section
/-! # Binders: specialization, existential introduction and alpha-renaming

For a body `q` with bound-label vector `E`, write `A z` for the translation of
`q` with `z` pushed onto `E`. If `x` occurs nowhere in `A y` and neither label is
bound in `q`'s translation, then `∀x A x → A y` and `A y → ∃x A x`; if moreover
`y` occurs nowhere in `A x`, then `∀x A x ↔ ∀y A y`. Iterating the last step
gives `tr_alpha`: translations in the two families, at any depths, are
equivalent. -/
namespace ZF207.Internal.Tait
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CKernel.Generic

namespace IntLogic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {L : IntLogic V}
open Logic

lemma sub_mp {a b A A' : V} (h : L.SubEq a b A A') :
    L.S.Prov (L.S.imp (L.S.E a b) (L.S.imp A A')) :=
  (sub_iff.mp h).andLeft.deduction.empty

lemma sub_mpr {a b A A' : V} (h : L.SubEq a b A A') :
    L.S.Prov (L.S.imp (L.S.E a b) (L.S.imp A' A)) :=
  (sub_iff.mp h).andRight.deduction.empty

lemma vac_prov {x a : V} (h : L.Vac x a) : L.S.Prov (L.S.imp a (L.S.all x a)) := vac_iff.mp h

/-- Specialization of `∀x A` at `y`. -/
lemma specialize {x y A A' : V} (hxy : x ≠ y) (hx : x ≠ rlab 0) (hy : y ≠ rlab 0)
    (sub : L.SubEq y x A' A) (vac : L.Vac x A') : L.Pr (imp (all x A) A') := by
  rw [pr_iff]
  simpa using L.S.specialize hxy ((L.ok_iff x).mpr hx) ((L.ok_iff y).mpr hy) (sub_mpr sub)
    (vac_prov vac)

/-- Existential introduction at `y`. -/
lemma exIntro {x y A A' : V} (hxy : x ≠ y) (hx : x ≠ rlab 0) (hy : y ≠ rlab 0)
    (sub : L.SubEq y x A' A) (vac : L.Vac x A') : L.Pr (imp A' (cex x A)) := by
  rw [pr_iff]
  simpa using L.S.exIntro hxy ((L.ok_iff x).mpr hx) ((L.ok_iff y).mpr hy) (sub_mp sub)
    (vac_prov vac)

/-- Renaming the bound label of `∀`. -/
lemma alphaAll {x y A B : V} (hxy : x ≠ y) (hx : x ≠ rlab 0) (hy : y ≠ rlab 0)
    (subxy : L.SubEq y x B A) (subyx : L.SubEq x y A B)
    (vacA : L.Vac y A) (vacB : L.Vac x B) :
    L.Pr (ciff (all x A) (all y B)) := by
  have h₁ : L.S.Prov (L.S.imp (L.S.all x A) B) := by
    simpa [pr_iff] using specialize hxy hx hy subxy vacB
  have h₂ : L.S.Prov (L.S.imp (L.S.all y B) A) := by
    simpa [pr_iff] using specialize hxy.symm hy hx subyx vacA
  have v₁ : L.S.Prov (L.S.imp (L.S.all x A) (L.S.all y (L.S.all x A))) :=
    L.S.toLogic.universalVacuity y x A (vac_prov vacA)
  have v₂ : L.S.Prov (L.S.imp (L.S.all y B) (L.S.all x (L.S.all y B))) :=
    L.S.toLogic.universalVacuity x y B (vac_prov vacB)
  have c₁ : L.S.toLogic.Ctx [L.S.all x A] (L.S.all y B) :=
    .mp (.mp Ctx.head (.thm v₁)) (.mp (.thm (L.S.gen y h₁)) (.thm (L.S.r2 _ _ _)))
  have c₂ : L.S.toLogic.Ctx [L.S.all y B] (L.S.all x A) :=
    .mp (.mp Ctx.head (.thm v₂)) (.mp (.thm (L.S.gen x h₂)) (.thm (L.S.r2 _ _ _)))
  rw [pr_iff]; simpa using (Ctx.iffIntro c₁ c₂).empty

lemma iff_refl' (A : V) : L.Pr (ciff A A) := by
  rw [pr_iff]; simpa using (Ctx.iffRefl (S := L.S.toLogic) (Γ := []) A).empty

lemma iff_trans' {A B C : V} (h₁ : L.Pr (ciff A B)) (h₂ : L.Pr (ciff B C)) : L.Pr (ciff A C) := by
  rw [pr_iff] at *
  have := Ctx.iffTrans (S := L.S.toLogic) (Γ := []) (.thm (by simpa using h₁)) (.thm (by simpa using h₂))
  simpa using this.empty

lemma iff_neg' {A B : V} (h : L.Pr (ciff A B)) : L.Pr (ciff (cneg A) (cneg B)) := by
  rw [pr_iff] at *
  simpa using (Ctx.negCongr (S := L.S.toLogic) (Γ := []) (.thm (by simpa using h))).empty

lemma iff_and' {A A' B B' : V} (h₁ : L.Pr (ciff A A')) (h₂ : L.Pr (ciff B B')) :
    L.Pr (ciff (cand A B) (cand A' B')) := by
  rw [pr_iff] at *
  simpa using (Ctx.andCongr (S := L.S.toLogic) (Γ := []) (.thm (by simpa using h₁))
    (.thm (by simpa using h₂))).empty

lemma iff_all' (x : V) {A B : V} (h : L.Pr (ciff A B)) : L.Pr (ciff (all x A) (all x B)) := by
  rw [pr_iff] at *; simpa using L.S.toLogic.allIff x (by simpa using h)

end IntLogic

/-! ## Labels of the two families -/

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] lemma xlab_inj {f f' d d' : V} : xlab f d = xlab f' d' ↔ f = f' ∧ d = d' := by
  simp [xlab]

@[simp] lemma xlab_ne_ylab (f d j : V) : xlab f d ≠ ylab j := by
  simp [xlab, ylab]

@[simp] lemma ylab_ne_xlab (f d j : V) : ylab j ≠ xlab f d := (xlab_ne_ylab f d j).symm

@[simp] lemma xlab_ne_zero (f d : V) : xlab f d ≠ 0 := by simp [xlab]

@[simp] lemma xlab_ne_rlab (f d k : V) : xlab f d ≠ rlab k := by
  have h2 : (1 : V) < f + 2 := lt_of_lt_of_le one_lt_two (le_add_of_nonneg_left (by simp))
  simp [xlab, rlab, h2.ne']

end

end ZF207.Internal.Tait
