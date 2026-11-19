module
public import Internal.Tait.Kernel
@[expose] public section
/-! # Vacuity of translations in foreign labels

A label is foreign to the parameters `⟪env, d, m, f⟫` if it is not `0`, not an
entry of `env`, not a label bound at depth `d` or deeper in family `f`, and not
a free-variable label from offset `m` on. Such a label occurs nowhere in the
translation, and the translation is vacuous in it. -/
namespace ZF207.Internal.Tait
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CKernel.Generic

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance rlab_definable' (Γ m) : Γᴬ_[m + 1]-Function₁ (rlab : V → V) :=
  .of_sigmaOne (.of_zero rlab_defined.to_definable)

instance xlab_definable' (Γ m) : Γᴬ_[m + 1]-Function₂ (xlab : V → V → V) :=
  .of_sigmaOne (.of_zero xlab_defined.to_definable)

instance ylab_definable' (Γ m) : Γᴬ_[m + 1]-Function₁ (ylab : V → V) :=
  .of_sigmaOne (.of_zero ylab_defined.to_definable)

/-- `x` occurs in no translation with parameters `⟪e, d, m, f⟫`. -/
def Foreign (x e d m f : V) : Prop :=
  x ≠ 0 ∧ (∀ i < len e, e.[i] ≠ x) ∧ (∀ d' ≤ x, d ≤ d' → x ≠ xlab f d') ∧
    (∀ j ≤ x, x ≠ ylab (m + j)) ∧ (x ≠ rlab 0 ∧ x ≠ rlab 1 ∧ x ≠ rlab 2)

instance foreign_definable : 𝚫ᴬ₁-Relation₅ (Foreign : V → V → V → V → V → Prop) := by
  unfold Foreign; definability

instance foreign_definable' (Γ m) : Γᴬ_[m + 1]-Relation₅ (Foreign : V → V → V → V → V → Prop) :=
  foreign_definable.of_deltaOne

lemma Foreign.ne_zero {x e d m f : V} (h : Foreign x e d m f) : x ≠ 0 := h.1

lemma Foreign.nth_ne {x e d m f : V} (h : Foreign x e d m f) (i : V) : e.[i] ≠ x := by
  by_cases hi : i < len e
  · exact h.2.1 i hi
  · rw [nth_lt_len (not_lt.mp hi)]; exact fun h0 => h.1 h0.symm

lemma Foreign.ne_xlab {x e d m f : V} (h : Foreign x e d m f) {d' : V} (hd : d ≤ d') :
    x ≠ xlab f d' := by
  by_cases hx : d' ≤ x
  · exact h.2.2.1 d' hx hd
  · intro e'
    have : d' ≤ x := by
      rw [e']; exact le_trans (le_pair_right _ _) (le_add_of_nonneg_right (by simp))
    exact hx this

lemma Foreign.ne_ylab {x e d m f : V} (h : Foreign x e d m f) (j : V) : x ≠ ylab (m + j) := by
  by_cases hx : j ≤ x
  · exact h.2.2.2.1 j hx
  · intro e'
    have : j ≤ x := by
      rw [e']
      exact le_trans (le_add_of_nonneg_left (by simp)) (le_trans (le_pair_right _ _)
        (le_add_of_nonneg_right (by simp)))
    exact hx this

lemma Foreign.step {x e d m f : V} (h : Foreign x e d m f) :
    Foreign x (xlab f d ∷ e) (d + 1) m f := by
  refine ⟨h.1, ?_, ?_, ?_, h.2.2.2.2⟩
  · intro i _
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · simpa using (h.ne_xlab le_rfl).symm
    · simpa using h.nth_ne i
  · intro d' _ hd; exact h.ne_xlab (le_trans (by simp) hd)
  · intro j _; exact h.ne_ylab j

lemma Foreign.res {x e d m f : V} (h : Foreign x e d m f) :
    x ≠ rlab 0 ∧ x ≠ rlab 1 ∧ x ≠ rlab 2 := h.2.2.2.2

lemma Foreign.vlab_ne {x e d m f t : V} (h : Foreign x e d m f) (ht : IsUTerm ℒₛₑₜ t) :
    vlab e m t ≠ x := by
  rcases set_uterm_cases ht with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simpa using h.nth_ne i
  · simpa using (h.ne_ylab i).symm

end

namespace IntLogic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (L : IntLogic V)

instance pr_definable_two (Γ) : Γᴬ_[2]-Predicate L.Pr :=
  Bounding.HierarchySymbol.Definable.of_lt (pr_definable L) (by simp)

/-- `a` is vacuous in `x`. -/
def Vac (x a : V) : Prop := L.Pr (imp a (all x a))

variable {L}

lemma vac_iff {x a : V} : L.Vac x a ↔ L.S.Prov (L.S.imp a (L.S.all x a)) := by
  simp [Vac, pr_iff]

lemma vac_imp {x a b : V} (ha : L.Vac x a) (hb : L.Vac x b) : L.Vac x (imp a b) := by
  rw [vac_iff] at *
  simpa using L.S.toLogic.implicationVacuity x a b (by simpa using ha) (by simpa using hb)

lemma vac_neg {x a : V} (ha : L.Vac x a) : L.Vac x (cneg a) := by
  rw [vac_iff] at *
  simpa using L.S.toLogic.negationVacuity x a (by simpa using ha)

lemma vac_and {x a b : V} (ha : L.Vac x a) (hb : L.Vac x b) : L.Vac x (cand a b) := by
  rw [vac_iff] at *
  simpa using L.S.toLogic.andVacuity x a b (by simpa using ha) (by simpa using hb)

lemma vac_all {x a : V} (y : V) (ha : L.Vac x a) : L.Vac x (all y a) := by
  rw [vac_iff] at *
  simpa using L.S.toLogic.universalVacuity x y a (by simpa using ha)

lemma vac_mem {x a b : V} (ha : x ≠ a) (hb : x ≠ b) : L.Vac x (mem a b) := by
  rw [vac_iff]; simpa using L.S.memVac a b x ha hb

lemma vac_bot {x : V} (hx : x ≠ 0) : L.Vac x 1 := by
  have hc : cantor (0 : V) 0 = 0 := by
    have h := two_mul_cantor (0 : V) 0
    simpa using h
  have : (1 : V) = mem 0 0 := by simp [mem, hc]
  rw [this]; exact vac_mem hx hx

lemma vac_iff' {x a b : V} (ha : L.Vac x a) (hb : L.Vac x b) : L.Vac x (ciff a b) :=
  vac_and (vac_imp ha hb) (vac_imp hb ha)

lemma vac_cex {x a : V} (y : V) (ha : L.Vac x a) : L.Vac x (cex y a) :=
  vac_neg (vac_all y (vac_neg ha))

lemma vac_ceqv {x a b : V} (hz : x ≠ rlab 0) (ha : x ≠ a) (hb : x ≠ b) : L.Vac x (ceqv a b) :=
  vac_and (vac_all _ (vac_iff' (vac_mem hz ha) (vac_mem hz hb)))
    (vac_all _ (vac_iff' (vac_mem ha hz) (vac_mem hb hz)))

lemma vac_atomL {x R a b : V} (hr : x ≠ rlab 0 ∧ x ≠ rlab 1 ∧ x ≠ rlab 2) (ha : x ≠ a)
    (hb : x ≠ b) : L.Vac x (atomL R a b) := by
  unfold atomL
  split
  · exact vac_ceqv hr.1 ha hb
  · exact vac_cex _ (vac_cex _ (vac_and (vac_and (vac_ceqv hr.1 ha hr.2.1)
      (vac_ceqv hr.1 hb hr.2.2)) (vac_mem hr.2.1 hr.2.2)))

lemma vac_atom {x e m R t₀ t₁ : V} (hr : x ≠ rlab 0 ∧ x ≠ rlab 1 ∧ x ≠ rlab 2)
    (h₀ : vlab e m t₀ ≠ x) (h₁ : vlab e m t₁ ≠ x) : L.Vac x (atom e m R t₀ t₁) :=
  vac_atomL hr (Ne.symm h₀) (Ne.symm h₁)

end IntLogic

/-! ## Vacuity of translations -/

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (L : IntLogic V)
open IntLogic

/-- Both components of a translation are vacuous in a foreign label. -/
theorem tr_vac {p : V} (hp : IsUFormula ℒₛₑₜ p) : ∀ e d m f x : V, Foreign x e d m f →
    L.Vac x (π₁ (tr ⟪e, d, m, f⟫ p)) ∧ L.Vac x (π₂ (tr ⟪e, d, m, f⟫ p)) := by
  revert p
  apply uformula_induction 𝚷 1 (P := fun p => ∀ e d m f x : V, Foreign x e d m f →
    L.Vac x (π₁ (tr ⟪e, d, m, f⟫ p)) ∧ L.Vac x (π₂ (tr ⟪e, d, m, f⟫ p)))
  · unfold Vac; definability
  · intro k r v hr hv e d m f x hx
    have hk := rel_two hr; subst hk
    have ha : L.Vac x (atom e m r v.[0] v.[1]) :=
      vac_atom hx.res (hx.vlab_ne (hv.nth (by simp))) (hx.vlab_ne (hv.nth (by simp)))
    simp only [tr_rel hr hv, posPair, pi₁_pair, pi₂_pair, penv_mk, poff_mk]
    exact ⟨ha, vac_neg ha⟩
  · intro k r v hr hv e d m f x hx
    have hk := rel_two hr; subst hk
    have ha : L.Vac x (atom e m r v.[0] v.[1]) :=
      vac_atom hx.res (hx.vlab_ne (hv.nth (by simp))) (hx.vlab_ne (hv.nth (by simp)))
    simp only [tr_nrel hr hv, negPair, pi₁_pair, pi₂_pair, penv_mk, poff_mk]
    exact ⟨vac_neg ha, ha⟩
  · intro e d m f x hx
    simp only [tr_verum, posPair, pi₁_pair, pi₂_pair]
    exact ⟨vac_neg (vac_bot hx.ne_zero), vac_neg (vac_neg (vac_bot hx.ne_zero))⟩
  · intro e d m f x hx
    simp only [tr_falsum, negPair, pi₁_pair, pi₂_pair]
    exact ⟨vac_neg (vac_neg (vac_bot hx.ne_zero)), vac_neg (vac_bot hx.ne_zero)⟩
  · intro p q hp hq ihp ihq e d m f x hx
    have hp' := ihp e d m f x hx; have hq' := ihq e d m f x hx
    simp only [tr_and hp hq, posPair, pi₁_pair, pi₂_pair]
    exact ⟨vac_and hp'.1 hq'.1, vac_neg (vac_and hp'.1 hq'.1)⟩
  · intro p q hp hq ihp ihq e d m f x hx
    have hp' := ihp e d m f x hx; have hq' := ihq e d m f x hx
    simp only [tr_or hp hq, negPair, pi₁_pair, pi₂_pair]
    exact ⟨vac_neg (vac_and hp'.2 hq'.2), vac_and hp'.2 hq'.2⟩
  · intro p hp ih e d m f x hx
    have h := ih (xlab f d ∷ e) (d + 1) m f x hx.step
    simp only [tr_all hp, posPair, pi₁_pair, pi₂_pair, step_mk, pfam_mk, pdep_mk]
    exact ⟨vac_all _ h.1, vac_neg (vac_all _ h.1)⟩
  · intro p hp ih e d m f x hx
    have h := ih (xlab f d ∷ e) (d + 1) m f x hx.step
    simp only [tr_exs hp, negPair, pi₁_pair, pi₂_pair, step_mk, pfam_mk, pdep_mk]
    exact ⟨vac_neg (vac_all _ h.2), vac_all _ h.2⟩

end

end ZF207.Internal.Tait
