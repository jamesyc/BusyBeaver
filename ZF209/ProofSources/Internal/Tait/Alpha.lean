module
public import Internal.Tait.Binder
@[expose] public section
/-! # Alpha-equivalence of translations

Translations of the same formula in two different families, at any depths, are
equivalent, provided the labels of the bound-label vector are bound in neither.
Composing two such steps changes the depth within one family. -/
namespace ZF209.Internal.Tait
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CKernel.Generic

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The labels of `E` are bound in neither translation. -/
def EnvFree (E d f d' f' : V) : Prop := ∀ i < len E, Unbound E.[i] d f ∧ Unbound E.[i] d' f'

instance envFree_definable : 𝚫ᴬ₁-Relation₅ (EnvFree : V → V → V → V → V → Prop) := by
  unfold EnvFree; definability

instance envFree_definable' (Γ m) : Γᴬ_[m + 1]-Relation₅ (EnvFree : V → V → V → V → V → Prop) :=
  envFree_definable.of_deltaOne

lemma unbound_xlab_self (f d : V) : Unbound (xlab f d) (d + 1) f := by
  intro d'' _ hd h
  have := (xlab_inj.mp h).2
  subst this
  exact absurd hd (by simp)

lemma unbound_xlab_other {f f' : V} (h : f ≠ f') (d d₀ : V) : Unbound (xlab f' d) d₀ f := by
  intro d'' _ _ e
  exact h (xlab_inj.mp e).1.symm

lemma EnvSub.head (a b E : V) : EnvSub a b (a ∷ E) (b ∷ E) := by
  refine ⟨by simp, ?_⟩
  intro i _
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp
  · simp

lemma EnvFree.nth_ne {E d f d' f' : V} (h : EnvFree E d f d' f') (i : V) :
    E.[i] ≠ xlab f d ∧ E.[i] ≠ xlab f' d' := by
  by_cases hi : i < len E
  · exact ⟨(h i hi).1.ne le_rfl, (h i hi).2.ne le_rfl⟩
  · rw [nth_lt_len (not_lt.mp hi)]; exact ⟨(xlab_ne_zero _ _).symm, (xlab_ne_zero _ _).symm⟩

/-- The label bound by the other family is foreign to a translation in one family. -/
lemma foreign_cross {E d f d' f' m : V} (hf : f ≠ f') (h : EnvFree E d f d' f') :
    Foreign (xlab f' d') (xlab f d ∷ E) (d + 1) m f := by
  refine ⟨xlab_ne_zero _ _, ?_, ?_, ?_, ?_⟩
  · intro i _
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · simp only [nth_adjoin_zero, ne_eq, xlab_inj, not_and]
      intro e; exact absurd e hf
    · simpa using (h.nth_ne i).2
  · intro d'' _ _ e; exact hf (xlab_inj.mp e).1.symm
  · intro j _; exact xlab_ne_ylab _ _ _
  · exact ⟨xlab_ne_rlab _ _ _, xlab_ne_rlab _ _ _, xlab_ne_rlab _ _ _⟩

/-- The label bound at depth `d` is foreign to the translation of the body with
another label pushed instead. -/
lemma foreign_self {E d f d' f' m : V} (hf : f ≠ f') (h : EnvFree E d f d' f') :
    Foreign (xlab f d) (xlab f' d' ∷ E) (d + 1) m f := by
  refine ⟨xlab_ne_zero _ _, ?_, ?_, ?_, ?_⟩
  · intro i _
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · simp only [nth_adjoin_zero, ne_eq, xlab_inj, not_and]
      intro e; exact absurd e.symm hf
    · simpa using (h.nth_ne i).1
  · intro d'' _ hd e
    have := (xlab_inj.mp e).2
    subst this
    exact absurd hd (by simp)
  · intro j _; exact xlab_ne_ylab _ _ _
  · exact ⟨xlab_ne_rlab _ _ _, xlab_ne_rlab _ _ _, xlab_ne_rlab _ _ _⟩

lemma EnvFree.step {E d f d' f' : V} (hf : f ≠ f') (h : EnvFree E d f d' f') :
    EnvFree (xlab f' d' ∷ E) (d + 1) f (d' + 1) f' := by
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp only [nth_adjoin_zero]
    exact ⟨unbound_xlab_other hf _ _, unbound_xlab_self _ _⟩
  · have hi' : i < len E := by simpa using hi
    simp only [nth_adjoin_succ]
    exact ⟨(h i hi').1.step, (h i hi').2.step⟩

end

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (L : IntLogic V)
open IntLogic

/-- Translations in different families are equivalent. -/
theorem tr_alpha {q : V} (hq : IsUFormula ℒₛₑₜ q) : ∀ E d d' m f f' : V, f ≠ f' →
    EnvFree E d f d' f' → EnvNotRes E →
    L.Pr (ciff (π₁ (tr ⟪E, d, m, f⟫ q)) (π₁ (tr ⟪E, d', m, f'⟫ q))) ∧
      L.Pr (ciff (π₂ (tr ⟪E, d, m, f⟫ q)) (π₂ (tr ⟪E, d', m, f'⟫ q))) := by
  revert q
  apply uformula_induction 𝚷 1 (P := fun q => ∀ E d d' m f f' : V, f ≠ f' →
    EnvFree E d f d' f' → EnvNotRes E →
    L.Pr (ciff (π₁ (tr ⟪E, d, m, f⟫ q)) (π₁ (tr ⟪E, d', m, f'⟫ q))) ∧
      L.Pr (ciff (π₂ (tr ⟪E, d, m, f⟫ q)) (π₂ (tr ⟪E, d', m, f'⟫ q))))
  · definability
  · intro k r v hr hv E d d' m f f' _ _ _
    simp only [tr_rel hr hv, penv_mk, poff_mk]
    exact ⟨iff_refl' _, iff_refl' _⟩
  · intro k r v hr hv E d d' m f f' _ _ _
    simp only [tr_nrel hr hv, penv_mk, poff_mk]
    exact ⟨iff_refl' _, iff_refl' _⟩
  · intro E d d' m f f' _ _ _
    simp only [tr_verum]; exact ⟨iff_refl' _, iff_refl' _⟩
  · intro E d d' m f f' _ _ _
    simp only [tr_falsum]; exact ⟨iff_refl' _, iff_refl' _⟩
  · intro p q hp hq ihp ihq E d d' m f f' hf hE hR
    have h₁ := ihp E d d' m f f' hf hE hR; have h₂ := ihq E d d' m f f' hf hE hR
    simp only [tr_and hp hq, posPair, pi₁_pair, pi₂_pair]
    exact ⟨iff_and' h₁.1 h₂.1, iff_neg' (iff_and' h₁.1 h₂.1)⟩
  · intro p q hp hq ihp ihq E d d' m f f' hf hE hR
    have h₁ := ihp E d d' m f f' hf hE hR; have h₂ := ihq E d d' m f f' hf hE hR
    simp only [tr_or hp hq, negPair, pi₁_pair, pi₂_pair]
    exact ⟨iff_neg' (iff_and' h₁.2 h₂.2), iff_and' h₁.2 h₂.2⟩
  · intro p hp ih E d d' m f f' hf hE hR
    have hRx := hR.step (notRes_xlab f d)
    have hRy := hR.step (notRes_xlab f' d')
    have ih' := ih (xlab f' d' ∷ E) (d + 1) (d' + 1) m f f' hf (hE.step hf) hRy
    have hs₁ := tr_sub L hp (xlab f' d') (xlab f d) _ _ (d + 1) m f (EnvSub.head _ _ E)
      (unbound_xlab_other hf _ _) (unbound_xlab_self _ _) (notRes_xlab _ _) (notRes_xlab _ _)
      hRy hRx
    have hs₂ := tr_sub L hp (xlab f d) (xlab f' d') _ _ (d + 1) m f (EnvSub.head _ _ E)
      (unbound_xlab_self _ _) (unbound_xlab_other hf _ _) (notRes_xlab _ _) (notRes_xlab _ _)
      hRx hRy
    have hv₁ := tr_vac L hp _ _ m f _ (foreign_cross (m := m) hf hE)
    have hv₂ := tr_vac L hp _ _ m f _ (foreign_self (m := m) hf hE)
    have hxy : xlab f d ≠ xlab f' d' := fun e => hf (xlab_inj.mp e).1
    have key := iff_trans' (alphaAll hxy (xlab_ne_rlab _ _ _) (xlab_ne_rlab _ _ _) hs₁.1 hs₂.1 hv₁.1 hv₂.1) (iff_all' (xlab f' d') ih'.1)
    simp only [tr_all hp, posPair, pi₁_pair, pi₂_pair, step_mk, pfam_mk, pdep_mk]
    exact ⟨key, iff_neg' key⟩
  · intro p hp ih E d d' m f f' hf hE hR
    have hRx := hR.step (notRes_xlab f d)
    have hRy := hR.step (notRes_xlab f' d')
    have ih' := ih (xlab f' d' ∷ E) (d + 1) (d' + 1) m f f' hf (hE.step hf) hRy
    have hs₁ := tr_sub L hp (xlab f' d') (xlab f d) _ _ (d + 1) m f (EnvSub.head _ _ E)
      (unbound_xlab_other hf _ _) (unbound_xlab_self _ _) (notRes_xlab _ _) (notRes_xlab _ _)
      hRy hRx
    have hs₂ := tr_sub L hp (xlab f d) (xlab f' d') _ _ (d + 1) m f (EnvSub.head _ _ E)
      (unbound_xlab_self _ _) (unbound_xlab_other hf _ _) (notRes_xlab _ _) (notRes_xlab _ _)
      hRx hRy
    have hv₁ := tr_vac L hp _ _ m f _ (foreign_cross (m := m) hf hE)
    have hv₂ := tr_vac L hp _ _ m f _ (foreign_self (m := m) hf hE)
    have hxy : xlab f d ≠ xlab f' d' := fun e => hf (xlab_inj.mp e).1
    have key := iff_trans' (alphaAll hxy (xlab_ne_rlab _ _ _) (xlab_ne_rlab _ _ _) hs₁.2 hs₂.2 hv₁.2 hv₂.2) (iff_all' (xlab f' d') ih'.2)
    simp only [tr_exs hp, negPair, pi₁_pair, pi₂_pair, step_mk, pfam_mk, pdep_mk]
    exact ⟨iff_neg' key, key⟩

end

end ZF209.Internal.Tait
