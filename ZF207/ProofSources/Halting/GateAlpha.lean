module
public import Internal.Tait.Binder
@[expose] public section
/-! # Renaming the binders of gate-shaped codes

`GF α n` is a small syntax with de Bruijn variables: membership atoms, an opaque binary relation,
falsity, implication and `∀` carrying a label of type `α`. `enc At Rf p ρ` is the code of `p` with
free variable `k` read as the label `ρ k`, atoms built by `At` and relation instances by `Rf`.

`alpha`: with raw membership on the left and membership up to `≈` on the right, the code of `p` is
C-equivalent to the code of `canon κ p d`, which relabels the binder at depth `d'` by `κ d'`. The
side conditions say that labels are not reserved, atoms have distinct arguments, no binder captures
a variable used beneath it, and original labels avoid the canonical ones below them. -/
namespace ZF207.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZF207.Internal ZF207.Internal.Tait ZF207.CKernel.Generic

/-- Gate-shaped formulas with binder labels in `α`. -/
inductive GF (α : Type) : ℕ → Type
  | mem {n} (i j : Fin n) : GF α n
  | rel {n} (i j : Fin n) : GF α n
  | bot {n} : GF α n
  | imp {n} (p q : GF α n) : GF α n
  | all {n} (x : α) (p : GF α (n + 1)) : GF α n

namespace GF
variable {α : Type}

/-- Variable `k` occurs in `p`. -/
def occ : {n : ℕ} → GF α n → Fin n → Prop
  | _, mem i j, k => k = i ∨ k = j
  | _, rel i j, k => k = i ∨ k = j
  | _, bot, _ => False
  | _, imp p q, k => occ p k ∨ occ q k
  | _, all _ p, k => occ p k.succ

/-- `z` is not a binder label of `p`. -/
def NotB (z : α) : {n : ℕ} → GF α n → Prop
  | _, mem _ _ => True
  | _, rel _ _ => True
  | _, bot => True
  | _, imp p q => NotB z p ∧ NotB z q
  | _, all x p => x ≠ z ∧ NotB z p

/-- Quantifier depth. -/
def depth : {n : ℕ} → GF α n → ℕ
  | _, mem _ _ => 0
  | _, rel _ _ => 0
  | _, bot => 0
  | _, imp p q => max (depth p) (depth q)
  | _, all _ p => depth p + 1

/-- Relabel the binder at depth `d` by `κ d`. -/
def canon {β : Type} (κ : ℕ → β) : {n : ℕ} → GF α n → ℕ → GF β n
  | _, mem i j, _ => mem i j
  | _, rel i j, _ => rel i j
  | _, bot, _ => bot
  | _, imp p q, d => imp (canon κ p d) (canon κ q d)
  | _, all _ p, d => all (κ d) (canon κ p (d + 1))

lemma occ_canon {β : Type} (κ : ℕ → β) : ∀ {n : ℕ} (p : GF α n) (d : ℕ) (k : Fin n),
    occ (canon κ p d) k ↔ occ p k
  | _, mem _ _, _, _ => Iff.rfl
  | _, rel _ _, _, _ => Iff.rfl
  | _, bot, _, _ => Iff.rfl
  | _, imp p q, d, k => by simp only [canon, occ, occ_canon κ p d k, occ_canon κ q d k]
  | _, all _ p, d, k => by simp only [canon, occ, occ_canon κ p (d + 1) k.succ]

lemma notB_canon {β : Type} (κ : ℕ → β) {z : β} : ∀ {n : ℕ} (p : GF α n) (d : ℕ),
    (∀ d', d ≤ d' → d' < d + depth p → κ d' ≠ z) → NotB z (canon κ p d)
  | _, mem _ _, _, _ => trivial
  | _, rel _ _, _, _ => trivial
  | _, bot, _, _ => trivial
  | _, imp p q, d, h => ⟨notB_canon κ p d fun d' h₁ h₂ => h d' h₁ (by simp [depth]; omega),
      notB_canon κ q d fun d' h₁ h₂ => h d' h₁ (by simp [depth]; omega)⟩
  | _, all _ p, d, h => ⟨h d le_rfl (by simp [depth]),
      notB_canon κ p (d + 1) fun d' h₁ h₂ => h d' (by omega) (by simp [depth]; omega)⟩

end GF

section Enc
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The code of a gate-shaped formula. -/
noncomputable def enc (At Rf : V → V → V) : {n : ℕ} → GF V n → (Fin n → V) → V
  | _, .mem i j, ρ => At (ρ i) (ρ j)
  | _, .rel i j, ρ => Rf (ρ i) (ρ j)
  | _, .bot, _ => 1
  | _, .imp p q, ρ => imp (enc At Rf p ρ) (enc At Rf q ρ)
  | _, .all x p, ρ => all x (enc At Rf p (x :> ρ))

/-- What the relation's codes must satisfy for labels with property `Fr`. -/
structure RelOK (L : IntLogic V) (Rf : V → V → V) (Fr : V → Prop) : Prop where
  sub : ∀ a b d h d' h', NotRes a → NotRes b → Fr a → Fr b → NotRes d → NotRes h → NotRes d' →
    NotRes h' → (d = d' ∨ (d = a ∧ d' = b)) → (h = h' ∨ (h = a ∧ h' = b)) →
    L.SubEq a b (Rf d h) (Rf d' h')
  vac : ∀ z d h, NotRes z → Fr z → z ≠ d → z ≠ h → L.Vac z (Rf d h)

variable {L : IntLogic V} {Rf : V → V → V} {Fr : V → Prop}
open IntLogic

/-- Binder labels of `p` are not reserved and satisfy `Fr`. -/
def BinOK (Fr : V → Prop) : {n : ℕ} → GF V n → Prop
  | _, .mem _ _ => True
  | _, .rel _ _ => True
  | _, .bot => True
  | _, .imp p q => BinOK Fr p ∧ BinOK Fr q
  | _, .all x p => NotRes x ∧ Fr x ∧ BinOK Fr p

lemma binOK_canon {κ : ℕ → V} (hκ : ∀ d, NotRes (κ d) ∧ Fr (κ d)) :
    ∀ {n : ℕ} (p : GF V n) (d : ℕ), BinOK Fr (GF.canon κ p d)
  | _, .mem _ _, _ => trivial
  | _, .rel _ _, _ => trivial
  | _, .bot, _ => trivial
  | _, .imp p q, d => ⟨binOK_canon hκ p d, binOK_canon hκ q d⟩
  | _, .all _ p, d => ⟨(hκ d).1, (hκ d).2, binOK_canon hκ p (d + 1)⟩

/-- Substitution in codes with membership up to `≈`. -/
theorem sub_enc (hR : RelOK L Rf Fr) {a b : V} (ha : NotRes a) (hb : NotRes b) (fa : Fr a)
    (fb : Fr b) : ∀ {n : ℕ} (p : GF V n) (ρ ρ' : Fin n → V), BinOK Fr p → p.NotB a → p.NotB b →
    (∀ k, NotRes (ρ k)) → (∀ k, NotRes (ρ' k)) →
    (∀ k, p.occ k → ρ k = ρ' k ∨ (ρ k = a ∧ ρ' k = b)) →
    L.SubEq a b (enc (atomL 1) Rf p ρ) (enc (atomL 1) Rf p ρ')
  | _, .mem i j, ρ, ρ', _, _, _, hρ, hρ', he =>
    sub_atomL 1 ha hb (hρ' i) (hρ j) (he i (Or.inl rfl)) (he j (Or.inr rfl))
  | _, .rel i j, ρ, ρ', _, _, _, hρ, hρ', he =>
    hR.sub a b _ _ _ _ ha hb fa fb (hρ i) (hρ j) (hρ' i) (hρ' j) (he i (Or.inl rfl))
      (he j (Or.inr rfl))
  | _, .bot, _, _, _, _, _, _, _, _ => sub_refl _ _ _
  | _, .imp p q, ρ, ρ', hB, hna, hnb, hρ, hρ', he =>
    sub_imp (sub_enc hR ha hb fa fb p ρ ρ' hB.1 hna.1 hnb.1 hρ hρ' fun k hk => he k (Or.inl hk))
      (sub_enc hR ha hb fa fb q ρ ρ' hB.2 hna.2 hnb.2 hρ hρ' fun k hk => he k (Or.inr hk))
  | _, .all x p, ρ, ρ', hB, hna, hnb, hρ, hρ', he => by
    refine sub_all x hB.1.1 hna.1 hnb.1 (sub_enc hR ha hb fa fb p _ _ hB.2.2 hna.2 hnb.2 ?_ ?_ ?_)
    · intro k; cases k using Fin.cases with
      | zero => exact hB.1
      | succ k => exact hρ k
    · intro k; cases k using Fin.cases with
      | zero => exact hB.1
      | succ k => exact hρ' k
    · intro k hk; cases k using Fin.cases with
      | zero => exact Or.inl rfl
      | succ k => exact he k hk

/-- Vacuity of codes with membership up to `≈`. -/
theorem vac_enc (hR : RelOK L Rf Fr) {z : V} (hz : NotRes z) (fz : Fr z) (hz0 : z ≠ 0) :
    ∀ {n : ℕ} (p : GF V n) (ρ : Fin n → V), p.NotB z → (∀ k, p.occ k → ρ k ≠ z) →
    L.Vac z (enc (atomL 1) Rf p ρ)
  | _, .mem i j, ρ, _, he =>
    vac_atomL hz (Ne.symm (he i (Or.inl rfl))) (Ne.symm (he j (Or.inr rfl)))
  | _, .rel i j, ρ, _, he => hR.vac z _ _ hz fz (Ne.symm (he i (Or.inl rfl)))
      (Ne.symm (he j (Or.inr rfl)))
  | _, .bot, _, _, _ => vac_bot hz0
  | _, .imp p q, ρ, hn, he =>
    vac_imp (vac_enc hR hz fz hz0 p ρ hn.1 fun k hk => he k (Or.inl hk))
      (vac_enc hR hz fz hz0 q ρ hn.2 fun k hk => he k (Or.inr hk))
  | _, .all x p, ρ, hn, he => by
    refine vac_all x (vac_enc hR hz fz hz0 p _ hn.2 ?_)
    intro k hk; cases k using Fin.cases with
    | zero => exact hn.1
    | succ k => exact he k hk

/-- Well-scoped labelling, relative to canonical labels `κ` from depth `d` on. -/
def WS (Fr : V → Prop) (κ : ℕ → V) (D : ℕ) : {n : ℕ} → GF V n → (Fin n → V) → ℕ → Prop
  | _, .mem i j, ρ, _ => ρ i ≠ ρ j
  | _, .rel _ _, _, _ => True
  | _, .bot, _, _ => True
  | _, .imp p q, ρ, d => WS Fr κ D p ρ d ∧ WS Fr κ D q ρ d
  | _, .all x p, ρ, d => NotRes x ∧ Fr x ∧ x ≠ 0 ∧ (∀ d', d < d' → d' < D → κ d' ≠ x) ∧
      (∀ k, p.occ k.succ → ρ k ≠ x) ∧ WS Fr κ D p (x :> ρ) (d + 1)

/-- Environments whose labels are not reserved and avoid the canonical labels from depth `d`. -/
def GEnvOK (κ : ℕ → V) (D : ℕ) {n : ℕ} (ρ : Fin n → V) (d : ℕ) : Prop :=
  ∀ k, NotRes (ρ k) ∧ ∀ d', d ≤ d' → d' < D → κ d' ≠ ρ k

/-- Renaming all binders to canonical labels, with raw membership replaced by membership up to
`≈`. -/
theorem alpha (hF1 : ∀ x y : V, x ≠ y → NotRes x → NotRes y → L.Pr (ciff (mem x y) (atomL 1 x y)))
    (hR : RelOK L Rf Fr) {κ : ℕ → V} (hκi : ∀ d d', κ d = κ d' → d = d')
    (hκ : ∀ d, NotRes (κ d) ∧ Fr (κ d) ∧ κ d ≠ 0) (D : ℕ) :
    ∀ {n : ℕ} (p : GF V n) (ρ : Fin n → V) (d : ℕ), d + p.depth ≤ D → WS Fr κ D p ρ d →
    GEnvOK κ D ρ d → L.Pr (ciff (enc mem Rf p ρ) (enc (atomL 1) Rf (GF.canon κ p d) ρ))
  | _, .mem i j, ρ, _, _, hw, he => hF1 _ _ hw (he i).1 (he j).1
  | _, .rel i j, ρ, _, _, _, _ => iff_refl' _
  | _, .bot, _, _, _, _, _ => iff_refl' _
  | _, .imp p q, ρ, d, hd, hw, he => by
    have h₁ := alpha hF1 hR hκi hκ D p ρ d (le_trans (by simp [GF.depth]) hd) hw.1 he
    have h₂ := alpha hF1 hR hκi hκ D q ρ d (le_trans (by simp [GF.depth]) hd) hw.2 he
    show L.Pr (ciff (imp (enc mem Rf p ρ) (enc mem Rf q ρ))
      (imp (enc (atomL 1) Rf (GF.canon κ p d) ρ) (enc (atomL 1) Rf (GF.canon κ q d) ρ)))
    rw [pr_iff] at *
    simpa using (Logic.Ctx.impCongr (S := L.S.toLogic) (Γ := []) (.thm (by simpa using h₁))
      (.thm (by simpa using h₂))).empty
  | _, .all x p, ρ, d, hd, hw, he => by
    obtain ⟨hxr, hxf, hx0, hxκ, hxo, hwp⟩ := hw
    have hd' : d + 1 + p.depth ≤ D := by simp [GF.depth] at hd; omega
    have he' : GEnvOK κ D (x :> ρ) (d + 1) := by
      intro k; cases k using Fin.cases with
      | zero => exact ⟨hxr, fun d' h₁ h₂ => hxκ d' (by omega) h₂⟩
      | succ k => exact ⟨(he k).1, fun d' h₁ h₂ => (he k).2 d' (by omega) h₂⟩
    have ih := alpha hF1 hR hκi hκ D p (x :> ρ) (d + 1) hd' hwp he'
    have s1 := iff_all' x ih
    show L.Pr (ciff (all x (enc mem Rf p (x :> ρ)))
      (all (κ d) (enc (atomL 1) Rf (GF.canon κ p (d + 1)) (κ d :> ρ))))
    by_cases hxk : x = κ d
    · subst hxk; exact s1
    refine iff_trans' s1 ?_
    have bκ : ∀ d', d + 1 ≤ d' → d' < d + 1 + p.depth → κ d' ≠ κ d := fun d' hd _ h => by
      have := hκi _ _ h; omega
    have bx : ∀ d', d + 1 ≤ d' → d' < d + 1 + p.depth → κ d' ≠ x := fun d' h₁ h₂ =>
      hxκ d' (by omega) (by omega)
    have hB := binOK_canon (Fr := Fr) (fun d => ⟨(hκ d).1, (hκ d).2.1⟩) p (d + 1)
    have nρx : ∀ k, NotRes ((x :> ρ) k) := fun k => (he' k).1
    have nρκ : ∀ k, NotRes ((κ d :> ρ) k) := by
      intro k; cases k using Fin.cases with
      | zero => exact (hκ d).1
      | succ k => exact (he k).1
    refine alphaAll hxk hxr.1 (hκ d).1.1 ?_ ?_ ?_ ?_
    · refine sub_enc hR (hκ d).1 hxr (hκ d).2.1 hxf _ _ _ hB (GF.notB_canon κ p _ bκ)
        (GF.notB_canon κ p _ bx) nρκ nρx ?_
      intro k _; cases k using Fin.cases with
      | zero => exact Or.inr ⟨rfl, rfl⟩
      | succ k => exact Or.inl rfl
    · refine sub_enc hR hxr (hκ d).1 hxf (hκ d).2.1 _ _ _ hB (GF.notB_canon κ p _ bx)
        (GF.notB_canon κ p _ bκ) nρx nρκ ?_
      intro k _; cases k using Fin.cases with
      | zero => exact Or.inr ⟨rfl, rfl⟩
      | succ k => exact Or.inl rfl
    · refine vac_enc hR (hκ d).1 (hκ d).2.1 (hκ d).2.2 _ _ (GF.notB_canon κ p _ bκ) ?_
      intro k _; cases k using Fin.cases with
      | zero => exact hxk
      | succ k => exact Ne.symm ((he k).2 d le_rfl (by omega))
    · refine vac_enc hR hxr hxf hx0 _ _ (GF.notB_canon κ p _ bx) ?_
      intro k hk; cases k using Fin.cases with
      | zero => exact Ne.symm hxk
      | succ k => exact hxo k ((GF.occ_canon κ p (d + 1) k.succ).mp hk)

end Enc

end ZF207.Halting
