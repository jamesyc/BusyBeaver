module
public import Internal.Tait.Vacuity
@[expose] public section
/-! # Substitution of a label in a translation

If two bound-label vectors agree except that some entries are `a` on one side
and `b` on the other, and neither `a` nor `b` is bound in the translation, then
`a = b` makes the two translations equivalent. With vacuity this gives
specialization and existential introduction at a binder. -/
namespace ZF209.Internal.Tait
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CKernel.Generic

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `e'` is `e` with some entries `a` replaced by `b`. -/
def EnvSub (a b e e' : V) : Prop :=
  len e = len e' ∧ ∀ i < len e, e.[i] = e'.[i] ∨ (e.[i] = a ∧ e'.[i] = b)

/-- `a` is not bound at depth `d` or deeper in family `f`. -/
def Unbound (a d f : V) : Prop := ∀ d' ≤ a, d ≤ d' → a ≠ xlab f d'

/-- `x` is not a reserved label. -/
def NotRes (x : V) : Prop := x ≠ rlab 0 ∧ x ≠ rlab 1 ∧ x ≠ rlab 2

/-- No entry of `e` is reserved. -/
def EnvNotRes (e : V) : Prop := ∀ i < len e, NotRes e.[i]

instance notRes_definable : 𝚫ᴬ₁-Predicate (NotRes : V → Prop) := by
  unfold NotRes; definability

instance notRes_definable' (Γ m) : Γᴬ_[m + 1]-Predicate (NotRes : V → Prop) :=
  notRes_definable.of_deltaOne

instance envNotRes_definable : 𝚫ᴬ₁-Predicate (EnvNotRes : V → Prop) := by
  unfold EnvNotRes NotRes; definability

instance envNotRes_definable' (Γ m) : Γᴬ_[m + 1]-Predicate (EnvNotRes : V → Prop) :=
  envNotRes_definable.of_deltaOne

@[simp] lemma rlab_inj {k k' : V} : rlab k = rlab k' ↔ k = k' := by simp [rlab]
@[simp] lemma rlab_ne_zero (k : V) : rlab k ≠ 0 := by simp [rlab]

lemma notRes_ylab (j : V) : NotRes (ylab j) := by simp [NotRes, ylab, rlab]
lemma notRes_xlab (f d : V) : NotRes (xlab f d) := by
  have h2 : (1 : V) < f + 2 := lt_of_lt_of_le one_lt_two (le_add_of_nonneg_left (by simp))
  simp [NotRes, xlab, rlab, h2.ne']

lemma EnvNotRes.nth {e : V} (h : EnvNotRes e) (i : V) : NotRes e.[i] := by
  by_cases hi : i < len e
  · exact h i hi
  · rw [nth_lt_len (not_lt.mp hi)]; simp [NotRes, (rlab_ne_zero _).symm]

lemma EnvNotRes.step {e x : V} (h : EnvNotRes e) (hx : NotRes x) : EnvNotRes (x ∷ e) := by
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simpa using hx
  · simpa using h.nth i

lemma EnvNotRes.vlab {e m t : V} (h : EnvNotRes e) (ht : IsUTerm ℒₛₑₜ t) : NotRes (vlab e m t) := by
  rcases set_uterm_cases ht with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simpa using h.nth i
  · simpa using notRes_ylab (m + i)

instance envSub_definable : 𝚫ᴬ₁-Relation₄ (EnvSub : V → V → V → V → Prop) := by
  unfold EnvSub; definability

instance envSub_definable' (Γ m) : Γᴬ_[m + 1]-Relation₄ (EnvSub : V → V → V → V → Prop) :=
  envSub_definable.of_deltaOne

instance unbound_definable : 𝚫ᴬ₁-Relation₃ (Unbound : V → V → V → Prop) := by
  unfold Unbound; definability

instance unbound_definable' (Γ m) : Γᴬ_[m + 1]-Relation₃ (Unbound : V → V → V → Prop) :=
  unbound_definable.of_deltaOne

lemma Unbound.ne {a d f : V} (h : Unbound a d f) {d' : V} (hd : d ≤ d') : a ≠ xlab f d' := by
  by_cases ha : d' ≤ a
  · exact h d' ha hd
  · intro e'
    have : d' ≤ a := by
      rw [e']; exact le_trans (le_pair_right _ _) (le_add_of_nonneg_right (by simp))
    exact ha this

lemma Unbound.step {a d f : V} (h : Unbound a d f) : Unbound a (d + 1) f :=
  fun d' _ hd => h.ne (le_trans (by simp) hd)

lemma EnvSub.step {a b e e' : V} (h : EnvSub a b e e') (x : V) : EnvSub a b (x ∷ e) (x ∷ e') := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp
  · simpa using h.2 i (by simpa using hi)

lemma EnvSub.nth {a b e e' : V} (h : EnvSub a b e e') (i : V) :
    e.[i] = e'.[i] ∨ (e.[i] = a ∧ e'.[i] = b) := by
  by_cases hi : i < len e
  · exact h.2 i hi
  · left
    rw [nth_lt_len (not_lt.mp hi), nth_lt_len (by rw [← h.1]; exact not_lt.mp hi)]

lemma EnvSub.vlab {a b e e' m t : V} (h : EnvSub a b e e') (ht : IsUTerm ℒₛₑₜ t) :
    vlab e m t = vlab e' m t ∨ (vlab e m t = a ∧ vlab e' m t = b) := by
  rcases set_uterm_cases ht with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simpa using h.nth i
  · simp

end

namespace IntLogic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (L : IntLogic V)

/-- Under `a = b`, `A` and `A'` are equivalent. -/
def SubEq (a b A A' : V) : Prop := L.Pr (imp (ceqv a b) (ciff A A'))

variable {L}
open Logic

lemma sub_iff {a b A A' : V} :
    L.SubEq a b A A' ↔ L.S.toLogic.Ctx [L.S.E a b] (L.S.iff A A') := by
  constructor
  · intro h
    exact .mp Ctx.head (.thm (by simpa [SubEq, pr_iff] using h))
  · intro h
    simpa [SubEq, pr_iff] using h.deduction.empty

lemma sub_refl (a b A : V) : L.SubEq a b A A := sub_iff.mpr (Ctx.iffRefl _)

lemma sub_imp {a b A A' B B' : V} (h₁ : L.SubEq a b A A') (h₂ : L.SubEq a b B B') :
    L.SubEq a b (imp A B) (imp A' B') := by
  rw [sub_iff] at *; simpa using Ctx.impCongr h₁ h₂

lemma sub_neg {a b A A' : V} (h : L.SubEq a b A A') : L.SubEq a b (cneg A) (cneg A') := by
  rw [sub_iff] at *; simpa using Ctx.negCongr h

lemma sub_and {a b A A' B B' : V} (h₁ : L.SubEq a b A A') (h₂ : L.SubEq a b B B') :
    L.SubEq a b (cand A B) (cand A' B') := by
  rw [sub_iff] at *; simpa using Ctx.andCongr h₁ h₂

lemma sub_all {a b A A' : V} (x : V) (hz : x ≠ rlab 0) (ha : x ≠ a) (hb : x ≠ b)
    (h : L.SubEq a b A A') : L.SubEq a b (all x A) (all x A') := by
  rw [sub_iff] at *
  have hv : ∀ h, h ∈ [L.S.E a b] → L.S.Prov (L.S.imp h (L.S.all x h)) := by
    intro h hh
    rw [List.mem_singleton.mp hh]
    simpa using vac_iff.mp (vac_ceqv (L := L) hz ha hb)
  simpa using Ctx.allCongr x hv h

lemma sub_ex {a b A A' : V} (x : V) (hz : x ≠ rlab 0) (ha : x ≠ a) (hb : x ≠ b)
    (h : L.SubEq a b A A') : L.SubEq a b (cex x A) (cex x A') :=
  sub_neg (sub_all x hz ha hb (sub_neg h))

lemma sub_trans {a b A B C : V} (h₁ : L.SubEq a b A B) (h₂ : L.SubEq a b B C) :
    L.SubEq a b A C := by
  rw [sub_iff] at *; exact Ctx.iffTrans h₁ h₂

lemma ok_of_notRes {x : V} (h : x ≠ rlab 0) : L.S.ok x := (L.ok_iff x).mpr h

lemma sub_ceqv_left {a b l l' w : V} (ha : NotRes a) (hb : NotRes b) (hw : w ≠ rlab 0)
    (h : l = l' ∨ (l = a ∧ l' = b)) : L.SubEq a b (ceqv l w) (ceqv l' w) := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · exact sub_refl _ _ _
  · simpa [SubEq, pr_iff] using L.S.eLeftIff (ok_of_notRes ha.1) (ok_of_notRes hb.1) (ok_of_notRes hw)

lemma sub_ceqv_right {a b l r r' : V} (ha : NotRes a) (hb : NotRes b) (hl : l ≠ rlab 0)
    (h : r = r' ∨ (r = a ∧ r' = b)) : L.SubEq a b (ceqv l r) (ceqv l r') := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · exact sub_refl _ _ _
  · simpa [SubEq, pr_iff] using L.S.eRightIff (ok_of_notRes ha.1) (ok_of_notRes hb.1) (ok_of_notRes hl)

lemma sub_atomL {a b l₀ l₀' l₁ l₁' : V} (R : V) (ha : NotRes a) (hb : NotRes b)
    (hl₀ : NotRes l₀') (hl₁ : NotRes l₁) (h₀ : l₀ = l₀' ∨ (l₀ = a ∧ l₀' = b))
    (h₁ : l₁ = l₁' ∨ (l₁ = a ∧ l₁' = b)) :
    L.SubEq a b (atomL R l₀ l₁) (atomL R l₀' l₁') := by
  have r₁ : rlab (1 : V) ≠ rlab 0 := by simp
  have r₂ : rlab (2 : V) ≠ rlab 0 := by simp
  unfold atomL
  split
  · exact sub_trans (sub_ceqv_left ha hb hl₁.1 h₀) (sub_ceqv_right ha hb hl₀.1 h₁)
  · refine sub_ex _ (by simp) (Ne.symm ha.2.1) (Ne.symm hb.2.1)
      (sub_ex _ (by simp) (Ne.symm ha.2.2) (Ne.symm hb.2.2)
        (sub_and (sub_and (sub_ceqv_left ha hb r₁ h₀) (sub_ceqv_left ha hb r₂ h₁)) (sub_refl _ _ _)))

end IntLogic

/-! ## Substitution in translations -/

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (L : IntLogic V)
open IntLogic

theorem tr_sub {p : V} (hp : IsUFormula ℒₛₑₜ p) : ∀ a b e e' d m f : V,
    EnvSub a b e e' → Unbound a d f → Unbound b d f → NotRes a → NotRes b →
    EnvNotRes e → EnvNotRes e' →
    L.SubEq a b (π₁ (tr ⟪e, d, m, f⟫ p)) (π₁ (tr ⟪e', d, m, f⟫ p)) ∧
      L.SubEq a b (π₂ (tr ⟪e, d, m, f⟫ p)) (π₂ (tr ⟪e', d, m, f⟫ p)) := by
  revert p
  apply uformula_induction 𝚷 1 (P := fun p => ∀ a b e e' d m f : V,
    EnvSub a b e e' → Unbound a d f → Unbound b d f → NotRes a → NotRes b →
    EnvNotRes e → EnvNotRes e' →
    L.SubEq a b (π₁ (tr ⟪e, d, m, f⟫ p)) (π₁ (tr ⟪e', d, m, f⟫ p)) ∧
      L.SubEq a b (π₂ (tr ⟪e, d, m, f⟫ p)) (π₂ (tr ⟪e', d, m, f⟫ p)))
  · unfold SubEq; definability
  · intro k r v hr hv a b e e' d m f he _ _ hna hnb hne hne'
    have hk := rel_two hr; subst hk
    have hA : L.SubEq a b (atom e m r v.[0] v.[1]) (atom e' m r v.[0] v.[1]) :=
      sub_atomL r hna hnb (hne'.vlab (hv.nth (by simp))) (hne.vlab (hv.nth (by simp)))
        (he.vlab (hv.nth (by simp))) (he.vlab (hv.nth (by simp)))
    simp only [tr_rel hr hv, posPair, pi₁_pair, pi₂_pair, penv_mk, poff_mk]
    exact ⟨hA, sub_neg hA⟩
  · intro k r v hr hv a b e e' d m f he _ _ hna hnb hne hne'
    have hk := rel_two hr; subst hk
    have hA : L.SubEq a b (atom e m r v.[0] v.[1]) (atom e' m r v.[0] v.[1]) :=
      sub_atomL r hna hnb (hne'.vlab (hv.nth (by simp))) (hne.vlab (hv.nth (by simp)))
        (he.vlab (hv.nth (by simp))) (he.vlab (hv.nth (by simp)))
    simp only [tr_nrel hr hv, negPair, pi₁_pair, pi₂_pair, penv_mk, poff_mk]
    exact ⟨sub_neg hA, hA⟩
  · intro a b e e' d m f _ _ _ _ _ _ _
    simp only [tr_verum]; exact ⟨sub_refl _ _ _, sub_refl _ _ _⟩
  · intro a b e e' d m f _ _ _ _ _ _ _
    simp only [tr_falsum]; exact ⟨sub_refl _ _ _, sub_refl _ _ _⟩
  · intro p q hp hq ihp ihq a b e e' d m f he ha hb hna hnb hne hne'
    have h₁ := ihp a b e e' d m f he ha hb hna hnb hne hne'
    have h₂ := ihq a b e e' d m f he ha hb hna hnb hne hne'
    simp only [tr_and hp hq, posPair, pi₁_pair, pi₂_pair]
    exact ⟨sub_and h₁.1 h₂.1, sub_neg (sub_and h₁.1 h₂.1)⟩
  · intro p q hp hq ihp ihq a b e e' d m f he ha hb hna hnb hne hne'
    have h₁ := ihp a b e e' d m f he ha hb hna hnb hne hne'
    have h₂ := ihq a b e e' d m f he ha hb hna hnb hne hne'
    simp only [tr_or hp hq, negPair, pi₁_pair, pi₂_pair]
    exact ⟨sub_neg (sub_and h₁.2 h₂.2), sub_and h₁.2 h₂.2⟩
  · intro p hp ih a b e e' d m f he ha hb hna hnb hne hne'
    have h := ih a b _ _ (d + 1) m f (he.step (xlab f d)) ha.step hb.step hna hnb
      (hne.step (notRes_xlab f d)) (hne'.step (notRes_xlab f d))
    simp only [tr_all hp, posPair, pi₁_pair, pi₂_pair, step_mk, pfam_mk, pdep_mk]
    have hA := sub_all (xlab f d) (notRes_xlab f d).1 (ha.ne le_rfl).symm (hb.ne le_rfl).symm h.1
    exact ⟨hA, sub_neg hA⟩
  · intro p hp ih a b e e' d m f he ha hb hna hnb hne hne'
    have h := ih a b _ _ (d + 1) m f (he.step (xlab f d)) ha.step hb.step hna hnb
      (hne.step (notRes_xlab f d)) (hne'.step (notRes_xlab f d))
    simp only [tr_exs hp, negPair, pi₁_pair, pi₂_pair, step_mk, pfam_mk, pdep_mk]
    have hA := sub_all (xlab f d) (notRes_xlab f d).1 (ha.ne le_rfl).symm (hb.ne le_rfl).symm h.2
    exact ⟨sub_neg hA, hA⟩

end

end ZF209.Internal.Tait
