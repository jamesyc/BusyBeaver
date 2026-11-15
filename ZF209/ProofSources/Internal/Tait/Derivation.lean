module
public import Internal.Tait.Sequent
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic
@[expose] public section
/-! # Foundation's internal derivations become C proofs

For a Δ1 theory `U` of `ℒₛₑₜ` whose axioms translate to C theorems, every
internal derivation of a sequent `s` gives a C proof of the translation of `s`.
The free-label offset `m` must lie in a window that shrinks by one at each
`∀`-rule (whose eigenvariable takes the label `Y (m - 1)`) and moves up by one at
each shift rule; the derivation code bounds both. -/
namespace ZF209.Internal.Tait
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CKernel.Generic

namespace IntLogic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (L : IntLogic V)

@[simp] lemma codes_imp (a b : V) : (codes : Codes V).imp a b = imp a b := rfl
@[simp] lemma codes_mem (a b : V) : (codes : Codes V).mem a b = mem a b := rfl
@[simp] lemma codes_eqc (a b : V) : (codes : Codes V).eq a b = eqc a b := rfl
@[simp] lemma codes_all (x a : V) : (codes : Codes V).all x a = all x a := rfl
@[simp] lemma codes_bot : (codes : Codes V).bot = 1 := rfl

/-- The calculus with the model's own code constructors. -/
noncomputable def T : EqLogic V where
  toCodes := codes
  Prov := L.Pr
  mp {a b} ha hab := by
    rw [pr_iff] at *; exact L.S.mp ha (by simpa using hab)
  gen x {a} ha := by rw [pr_iff] at *; simpa using L.S.gen x ha
  k a b := by rw [pr_iff]; simpa using L.S.k a b
  s a b c := by rw [pr_iff]; simpa using L.S.s a b c
  peirce a b := by rw [pr_iff]; simpa using L.S.peirce a b
  r2 d a h := by rw [pr_iff]; simpa using L.S.r2 d a h
  h1 d h := by rw [pr_iff]; simpa [Codes.head1, Codes.ex, Codes.neg] using L.S.h1 d h
  h2 d a h := by rw [pr_iff]; simpa [Codes.head2] using L.S.h2 d a h
  E := ceqv
  ok x := x ≠ rlab 0
  witness x y hxy hx hy := by
    rw [pr_iff]
    simpa using L.S.witness x y hxy ((L.ok_iff x).mpr hx) ((L.ok_iff y).mpr hy)
  eVac a b c hca hcb ha hb hc := by
    rw [pr_iff]
    simpa using L.S.eVac a b c hca hcb ((L.ok_iff a).mpr ha) ((L.ok_iff b).mpr hb)
      ((L.ok_iff c).mpr hc)
  memVac a b c hca hcb := by rw [pr_iff]; simpa using L.S.memVac a b c hca hcb
  eSymm a b ha hb := by
    rw [pr_iff]; simpa using L.S.eSymm a b ((L.ok_iff a).mpr ha) ((L.ok_iff b).mpr hb)
  eTrans a b d ha hb hd := by
    rw [pr_iff]
    simpa using L.S.eTrans a b d ((L.ok_iff a).mpr ha) ((L.ok_iff b).mpr hb) ((L.ok_iff d).mpr hd)

@[simp] lemma T_prov (x : V) : L.T.Prov x ↔ L.Pr x := Iff.rfl

end IntLogic

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The two components of a translation are complementary. -/
lemma tr_pair {q : V} (hq : IsUFormula ℒₛₑₜ q) (param : V) :
    π₂ (tr param q) = cneg (π₁ (tr param q)) ∨ π₁ (tr param q) = cneg (π₂ (tr param q)) := by
  rcases hq.case with ⟨k, r, v, hr, hv, rfl⟩ | ⟨k, r, v, hr, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩
  · simp [hr, hv, posPair]
  · simp [hr, hv, negPair]
  · simp [posPair]
  · simp [negPair]
  · simp [h₁, h₂, posPair]
  · simp [h₁, h₂, negPair]
  · simp [h₁, posPair]
  · simp [h₁, negPair]

lemma unbound_ylab (j d f : V) : Unbound (ylab j) d f := fun _ _ _ e => ylab_ne_xlab _ _ _ e

lemma envNotRes_one {x : V} (hx : NotRes x) : EnvNotRes (x ∷ (0 : V)) :=
  EnvNotRes.step (fun i hi => by simp at hi) hx

lemma envFree_ylab (j d f d' f' : V) : EnvFree (ylab j ∷ 0) d f d' f' := by
  intro i hi
  have : i = 0 := by simpa using hi
  subst this
  simp only [nth_adjoin_zero]
  exact ⟨unbound_ylab _ _ _, unbound_ylab _ _ _⟩

lemma foreign_ylab_sequent {m j : V} (hj : j < m) : Foreign (ylab j) 0 0 m 0 := by
  refine ⟨by simp [ylab], by simp, fun _ _ _ e => ylab_ne_xlab _ _ _ e, ?_, (notRes_ylab j)⟩
  intro i _ e
  have : j = m + i := by simpa [ylab] using e
  exact absurd (this ▸ hj) (by simp)

end

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma foreign_x_y (j m : V) : Foreign (xlab (0 : V) 0) (ylab j ∷ 0) 1 m 0 := by
  refine ⟨xlab_ne_zero _ _, ?_, ?_, fun _ _ => xlab_ne_ylab _ _ _, notRes_xlab _ _⟩
  · intro i hi
    have : i = 0 := by simpa using hi
    subst this; simpa using ylab_ne_xlab _ _ _
  · intro d' _ hd e
    have := (xlab_inj.mp e).2
    subst this; simp at hd

lemma foreign_y_x {j m : V} (hj : j < m) : Foreign (ylab j) (xlab (0 : V) 0 ∷ 0) 1 m 0 := by
  refine ⟨by simp [ylab], ?_, fun _ _ _ e => ylab_ne_xlab _ _ _ e, ?_, notRes_ylab j⟩
  · intro i hi
    have : i = 0 := by simpa using hi
    subst this; simpa using xlab_ne_ylab _ _ _
  · intro i _ e
    have : j = m + i := by simpa [ylab] using e
    exact absurd (this ▸ hj) (by simp)

end

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (L : IntLogic V)
open IntLogic Logic

/-! ## Propositional steps -/

lemma excluded {q : V} (hq : IsUFormula ℒₛₑₜ q) (param : V) :
    L.T.Prov (cor (π₁ (tr param q)) (π₂ (tr param q))) := by
  rcases tr_pair hq param with h | h
  · rw [h]; exact (Ctx.deduction (S := L.T.toLogic) (Γ := []) Ctx.head).empty
  · rw [h]
    have : L.T.toLogic.Ctx [cneg (cneg (π₂ (tr param q)))] (π₂ (tr param q)) := Ctx.head.dne
    exact this.deduction.empty

lemma contra {q : V} (hq : IsUFormula ℒₛₑₜ q) (param G : V) :
    L.T.Prov (imp (π₁ (tr param q)) (imp (π₂ (tr param q)) G)) := by
  rcases tr_pair hq param with h | h
  · rw [h]
    have c : L.T.toLogic.Ctx [cneg (π₁ (tr param q)), π₁ (tr param q)] G :=
      (Ctx.mp (Ctx.head.up _) Ctx.head).explosion G
    exact c.deduction.deduction.empty
  · rw [h]
    have c : L.T.toLogic.Ctx [π₂ (tr param q), cneg (π₂ (tr param q))] G :=
      (Ctx.mp Ctx.head (Ctx.head.up _)).explosion G
    exact c.deduction.deduction.empty

lemma seqC_insert {p s m : V} (h : L.T.Prov (seqC (insert p s) m)) :
    L.T.Prov (cor (chiS m p) (seqC s m)) := by
  refine L.T.mp h (seqC_elim L ?_)
  intro r hr
  rcases mem_bitInsert_iff.mp hr with rfl | hr
  · exact (Ctx.orInl (S := L.T.toLogic) (Γ := [chiS m r]) (seqC s m) Ctx.head).deduction.empty
  · exact (Ctx.orInr (S := L.T.toLogic) (chiS m p) (.mp Ctx.head (.thm (seqC_intro L hr)))
      : L.T.toLogic.Ctx [chiS m r] _).deduction.empty

/-- From `A ∨ G` and `A → G`, `G`. -/
lemma or_self_elim {A G : V} (h : L.T.Prov (cor A G)) (ha : L.T.Prov (imp A G)) : L.T.Prov G :=
  (Ctx.orElim (S := L.T.toLogic) (Γ := []) (.thm h) (.mp Ctx.head (.thm ha)) Ctx.head).empty

/-! ## The rules -/

variable {L}

lemma rule_axL {s p m : V} (hs : IsFormulaSet ℒₛₑₜ s) (hp : p ∈ s) (hn : neg ℒₛₑₜ p ∈ s) :
    L.T.Prov (seqC s m) := by
  have hq := (hs p hp).isUFormula
  have e : chiS m (neg ℒₛₑₜ p) = π₂ (tr ⟪0, 0, m, 0⟫ p) := ((tr_neg hq _).1).symm
  have h₁ := seqC_intro L hp (m := m)
  have h₂ := seqC_intro L hn (m := m)
  rw [e] at h₂
  exact (Ctx.orElim (S := L.T.toLogic) (Γ := []) (.thm (excluded L hq _))
    (.mp Ctx.head (.thm h₁)) (.mp Ctx.head (.thm h₂))).empty

lemma rule_verum {s m : V} (h : ^⊤ ∈ s) : L.T.Prov (seqC s m) := by
  have h₁ := seqC_intro L h (m := m)
  simp only [chiS, tr_verum, posPair, pi₁_pair] at h₁
  exact L.T.mp (Ctx.deduction (S := L.T.toLogic) (Γ := []) Ctx.head).empty h₁

lemma rule_and {s p q m : V} (hs : IsFormulaSet ℒₛₑₜ s) (h : p ^⋏ q ∈ s)
    (hp : L.T.Prov (seqC (insert p s) m)) (hq : L.T.Prov (seqC (insert q s) m)) :
    L.T.Prov (seqC s m) := by
  have hpq := IsSemiformula.and.mp (hs _ h)
  have h₀ := seqC_intro L h (m := m)
  simp only [chiS, tr_and hpq.1.isUFormula hpq.2.isUFormula, posPair, pi₁_pair] at h₀
  have a := seqC_insert L hp; have b := seqC_insert L hq
  simp only [chiS] at a b
  refine (Ctx.orElim (S := L.T.toLogic) (Γ := []) (.thm a) ?_ Ctx.head).empty
  refine Ctx.orElim ((Ctx.thm b).up _) ?_ Ctx.head
  exact .mp (Ctx.andIntro (Ctx.head.up _) Ctx.head) (.thm h₀)

lemma rule_or {s p q m : V} (hs : IsFormulaSet ℒₛₑₜ s) (h : p ^⋎ q ∈ s)
    (hd : L.T.Prov (seqC (insert p (insert q s)) m)) : L.T.Prov (seqC s m) := by
  have hpq := IsSemiformula.or.mp (hs _ h)
  have h₀ := seqC_intro L h (m := m)
  simp only [chiS, tr_or hpq.1.isUFormula hpq.2.isUFormula, negPair, pi₁_pair] at h₀
  have a := seqC_insert L hd
  have b : L.T.Prov (imp (seqC (insert q s) m) (cor (chiS m q) (seqC s m))) :=
    seqC_elim L (fun r hr => by
      rcases mem_bitInsert_iff.mp hr with rfl | hr
      · exact (Ctx.orInl (S := L.T.toLogic) (Γ := [chiS m r]) (seqC s m) Ctx.head).deduction.empty
      · exact (Ctx.orInr (S := L.T.toLogic) (chiS m q) (.mp Ctx.head (.thm (seqC_intro L hr)))
          : L.T.toLogic.Ctx [chiS m r] _).deduction.empty)
  have cp := contra L hpq.1.isUFormula ⟪0, 0, m, 0⟫ 1
  have cq := contra L hpq.2.isUFormula ⟪0, 0, m, 0⟫ 1
  simp only [chiS] at a b
  -- `A → ¬(A' ∧ B')` and `B → ¬(A' ∧ B')`.
  have na : L.T.toLogic.Ctx [π₁ (tr ⟪0, 0, m, 0⟫ p)]
      (cneg (cand (π₂ (tr ⟪0, 0, m, 0⟫ p)) (π₂ (tr ⟪0, 0, m, 0⟫ q)))) :=
    Ctx.deduction (.mp (Ctx.head.andLeft) (.mp (Ctx.head.up _) (.thm cp)))
  have nb : L.T.toLogic.Ctx [π₁ (tr ⟪0, 0, m, 0⟫ q)]
      (cneg (cand (π₂ (tr ⟪0, 0, m, 0⟫ p)) (π₂ (tr ⟪0, 0, m, 0⟫ q)))) :=
    Ctx.deduction (.mp (Ctx.head.andRight) (.mp (Ctx.head.up _) (.thm cq)))
  refine (Ctx.orElim (S := L.T.toLogic) (Γ := []) (.thm a) ?_ ?_).empty
  · exact .mp (na.cut fun b hb => by rw [List.mem_singleton.mp hb]; exact Ctx.head) (.thm h₀)
  · refine Ctx.orElim (.mp Ctx.head (.thm b)) ?_ Ctx.head
    exact .mp (nb.cut fun b hb => by rw [List.mem_singleton.mp hb]; exact Ctx.head) (.thm h₀)

lemma rule_wk {s s' m : V} (h : s' ⊆ s) (hd : L.T.Prov (seqC s' m)) : L.T.Prov (seqC s m) :=
  L.T.mp hd (seqC_elim L fun r hr => seqC_intro L (h hr))

lemma rule_shift {s m : V} (hs : IsFormulaSet ℒₛₑₜ s) (hd : L.T.Prov (seqC s (m + 1))) :
    L.T.Prov (seqC (setShift ℒₛₑₜ s) m) := by
  refine L.T.mp hd (seqC_elim L fun r hr => ?_)
  have e : chiS (m + 1) r = chiS m (shift ℒₛₑₜ r) := by
    simp [chiS, tr_shift (hs r hr).isUFormula]
  rw [e]; exact seqC_intro L (shift_mem_setShift hr)

lemma rule_cut {s p m : V} (hs : IsFormulaSet ℒₛₑₜ (insert p s))
    (h₁ : L.T.Prov (seqC (insert p s) m)) (h₂ : L.T.Prov (seqC (insert (neg ℒₛₑₜ p) s) m)) :
    L.T.Prov (seqC s m) := by
  have hq := (hs p (by simp)).isUFormula
  have a := seqC_insert L h₁
  have b := seqC_insert L h₂
  have e : chiS m (neg ℒₛₑₜ p) = π₂ (tr ⟪0, 0, m, 0⟫ p) := ((tr_neg hq _).1).symm
  rw [e] at b
  have c := contra L hq ⟪0, 0, m, 0⟫ (seqC s m)
  simp only [chiS] at a
  refine (Ctx.orElim (S := L.T.toLogic) (Γ := []) (.thm a) ?_ Ctx.head).empty
  exact Ctx.orElim ((Ctx.thm b).up _) (.mp Ctx.head (.mp (Ctx.head.up _) (.thm c))) Ctx.head

lemma rule_axm {s p m : V} (hp : p ∈ s) (hU : L.T.Prov (chiS m p)) : L.T.Prov (seqC s m) :=
  L.T.mp hU (seqC_intro L hp)

/-- Changing the depth of a translation with one free-variable label pushed. -/
lemma depth_change {p : V} (hp : IsUFormula ℒₛₑₜ p) (j m : V) :
    L.T.Prov (ciff (π₁ (tr ⟪ylab j ∷ 0, 0, m, 0⟫ p)) (π₁ (tr ⟪ylab j ∷ 0, 1, m, 0⟫ p))) :=
  iff_trans' (tr_alpha L hp _ 0 0 m 0 1 (by simp) (envFree_ylab _ _ _ _ _)
      (envNotRes_one (notRes_ylab _))).1
    (tr_alpha L hp _ 0 1 m 1 0 (by simp) (envFree_ylab _ _ _ _ _)
      (envNotRes_one (notRes_ylab _))).1

lemma rule_all {s p m : V} (hs : IsFormulaSet ℒₛₑₜ s) (h : ^∀ p ∈ s)
    (hd : L.T.Prov (seqC (insert (free ℒₛₑₜ p) (setShift ℒₛₑₜ s)) m)) :
    L.T.Prov (seqC s (m + 1)) := by
  have hp1 : IsSemiformula ℒₛₑₜ 1 p := by simpa using hs _ h
  have hp := hp1.isUFormula
  set G := seqC s (m + 1)
  set Y := ylab m
  set X := xlab (0 : V) 0
  have a := seqC_insert L hd
  have hsh : L.T.Prov (imp (seqC (setShift ℒₛₑₜ s) m) G) :=
    seqC_elim L fun r hr => by
      obtain ⟨q, hq, rfl⟩ := mem_setShift_iff.mp hr
      have e : chiS m (shift ℒₛₑₜ q) = chiS (m + 1) q := by
        simp [chiS, tr_shift (hs q hq).isUFormula]
      rw [e]; exact seqC_intro L hq
  have ef : chiS m (free ℒₛₑₜ p) = π₁ (tr ⟪Y ∷ 0, 0, m + 1, 0⟫ p) := by
    simp [chiS, tr_free hp1, Y]
  rw [ef] at a
  have dc := depth_change (L := L) hp m (m + 1)
  -- `¬G → A Y` with `A z := π₁ (tr ⟪z ∷ 0, 1, m + 1, 0⟫ p)`.
  have h₁ : L.T.toLogic.Ctx [cneg G] (π₁ (tr ⟪Y ∷ 0, 1, m + 1, 0⟫ p)) := by
    refine Ctx.orElim (.thm a) ?_ ?_
    · exact (Ctx.thm dc).iffMp Ctx.head
    · exact (Ctx.mp (Ctx.mp Ctx.head (.thm hsh)) (Ctx.head.up _)).explosion _
  have vG : L.Vac Y G :=
    seqC_vac L (by simp [Y, ylab]) fun q hq =>
      (tr_vac L (hs q hq).isUFormula 0 0 (m + 1) 0 Y (foreign_ylab_sequent (by simp))).1
  have h₂ : L.T.toLogic.Ctx [cneg G] (all Y (π₁ (tr ⟪Y ∷ 0, 1, m + 1, 0⟫ p))) :=
    h₁.generalize Y fun b hb => by
      rw [List.mem_singleton.mp hb]; exact vac_neg vG
  -- rename the binder to `X`
  have hs₁ := tr_sub L hp X Y _ _ 1 (m + 1) 0 (EnvSub.head _ _ 0)
    (by simpa using unbound_xlab_self (0 : V) 0) (unbound_ylab _ _ _) (notRes_xlab _ _)
    (notRes_ylab _) (envNotRes_one (notRes_xlab _ _)) (envNotRes_one (notRes_ylab _))
  have hs₂ := tr_sub L hp Y X _ _ 1 (m + 1) 0 (EnvSub.head _ _ 0)
    (unbound_ylab _ _ _) (by simpa using unbound_xlab_self (0 : V) 0) (notRes_ylab _)
    (notRes_xlab _ _) (envNotRes_one (notRes_ylab _)) (envNotRes_one (notRes_xlab _ _))
  have fX : Foreign X (Y ∷ 0) 1 (m + 1) 0 := foreign_x_y m (m + 1)
  have fY : Foreign Y (X ∷ 0) 1 (m + 1) 0 := foreign_y_x (by simp)
  have hv₁ := tr_vac L hp _ 1 (m + 1) 0 X fX
  have hv₂ := tr_vac L hp _ 1 (m + 1) 0 Y fY
  have al := alphaAll (ylab_ne_xlab _ _ _) (notRes_ylab _).1 (notRes_xlab _ _).1
    hs₁.1 hs₂.1 hv₁.1 hv₂.1
  have h₀ := seqC_intro L h (m := m + 1)
  simp only [chiS, tr_all hp, posPair, pi₁_pair, step_mk, pfam_mk, pdep_mk, zero_add] at h₀
  have h₃ : L.T.toLogic.Ctx [cneg G] G := .mp ((Ctx.thm al).iffMp h₂) (.thm h₀)
  exact (Ctx.byContra (.mp h₃ Ctx.head)).empty

lemma rule_exs {s p t m : V} (hs : IsFormulaSet ℒₛₑₜ s) (h : ^∃ p ∈ s) (ht : IsTerm ℒₛₑₜ t)
    (hd : L.T.Prov (seqC (insert (substs1 ℒₛₑₜ t p) s) m)) : L.T.Prov (seqC s m) := by
  have hp1 : IsSemiformula ℒₛₑₜ 1 p := by simpa using hs _ h
  have hp := hp1.isUFormula
  obtain ⟨j, rfl⟩ : ∃ j, t = ^&j := by
    rcases set_term_cases.mp ht with ⟨i, hi, _⟩ | h'
    · simp at hi
    · exact h'
  set G := seqC s m
  set Y := ylab (m + j)
  set X := xlab (0 : V) 0
  have a := seqC_insert L hd
  have ef : chiS m (substs1 ℒₛₑₜ ^&j p) = π₁ (tr ⟪Y ∷ 0, 0, m, 0⟫ p) := by
    simp [chiS, tr_substs1 hp1, Y]
  rw [ef] at a
  have dc := depth_change (L := L) hp (m + j) m
  have hs₁ := tr_sub L hp Y X _ _ 1 m 0 (EnvSub.head _ _ 0)
    (unbound_ylab _ _ _) (by simpa using unbound_xlab_self (0 : V) 0) (notRes_ylab _)
    (notRes_xlab _ _) (envNotRes_one (notRes_ylab _)) (envNotRes_one (notRes_xlab _ _))
  have fX : Foreign X (Y ∷ 0) 1 m 0 := foreign_x_y (m + j) m
  have hv := tr_vac L hp _ 1 m 0 X fX
  have sp := specialize (xlab_ne_ylab _ _ _) (notRes_xlab _ _).1 (notRes_ylab _).1 hs₁.2 hv.2
  have c := contra L hp ⟪Y ∷ 0, 1, m, 0⟫ 1
  have h₀ := seqC_intro L h (m := m)
  simp only [chiS, tr_exs hp, negPair, pi₁_pair, step_mk, pfam_mk, pdep_mk, zero_add] at h₀
  -- `A Y → ¬∀X B X`
  have na : L.T.toLogic.Ctx [π₁ (tr ⟪Y ∷ 0, 1, m, 0⟫ p)]
      (cneg (all X (π₂ (tr ⟪X ∷ 0, 1, m, 0⟫ p)))) :=
    Ctx.deduction (.mp (.mp Ctx.head (.thm sp)) (.mp (Ctx.head.up _) (.thm c)))
  refine (Ctx.orElim (S := L.T.toLogic) (Γ := []) (.thm a) ?_ Ctx.head).empty
  have hA : L.T.toLogic.Ctx [π₁ (tr ⟪Y ∷ 0, 0, m, 0⟫ p)] (π₁ (tr ⟪Y ∷ 0, 1, m, 0⟫ p)) :=
    (Ctx.thm dc).iffMp Ctx.head
  exact .mp (na.cut fun b hb => by rw [List.mem_singleton.mp hb]; exact hA) (.thm h₀)

/-! ## The induction -/

variable (L)

/-- Every internal derivation translates to a C proof of its sequent, at every
free-label offset in the window `d ≤ m`, `m + d ≤ M`. -/
theorem derivation_tr (U : Theory ℒₛₑₜ) [U.Δ₁]
    (hU : ∀ p ∈ U.Δ₁Class (V := V), ∀ m, L.T.Prov (chiS m p)) (M : V) {d : V}
    (hd : Derivation U d) : ∀ m ≤ M, d ≤ m → m + d ≤ M → L.Pr (seqC (fstIdx d) m) := by
  have hP : 𝚺ᴬ₁-Predicate (fun d : V => ∀ m ≤ M, d ≤ m → m + d ≤ M → L.Pr (seqC (fstIdx d) m)) := by
    unfold seqC; definability
  apply Derivation.induction1 𝚺 hP hd
  · intro s hs p hp hn m _ _ _
    simpa using rule_axL hs hp hn
  · intro s hs h m _ _ _
    simpa using rule_verum h
  · intro s hs p q dp dq hpq hdp hdq ihp ihq m hm hdm hmM
    have lp : dp < andIntro s p q dp dq := by simp
    have lq : dq < andIntro s p q dp dq := by simp
    simp only [fstIdx_andIntro]
    refine rule_and hs hpq ?_ ?_
    · simpa [hdp.1] using ihp m hm (le_trans lp.le hdm) (le_trans (add_le_add (le_refl m) lp.le) hmM)
    · simpa [hdq.1] using ihq m hm (le_trans lq.le hdm) (le_trans (add_le_add (le_refl m) lq.le) hmM)
  · intro s hs p q d₀ hpq hd₀ ih m hm hdm hmM
    have l : d₀ < orIntro s p q d₀ := by simp
    simp only [fstIdx_orIntro]
    exact rule_or hs hpq (by
      simpa [hd₀.1] using ih m hm (le_trans l.le hdm) (le_trans (add_le_add (le_refl m) l.le) hmM))
  · intro s hs p d₀ hp hd₀ ih m hm hdm hmM
    have l : d₀ < allIntro s p d₀ := by simp
    simp only [fstIdx_allIntro]
    rcases zero_or_succ m with rfl | ⟨m, rfl⟩
    · exact absurd (lt_of_lt_of_le l hdm) (by simp)
    · refine rule_all hs hp ?_
      have hd₀m : d₀ ≤ m := le_iff_lt_succ.mpr (lt_of_lt_of_le l hdm)
      simpa [hd₀.1] using ih m (le_trans (by simp) hm) hd₀m
        (le_trans (add_le_add (le_refl m) l.le)
          (le_trans (add_le_add (le_add_of_nonneg_right (by simp) : m ≤ m + 1) (le_refl _)) hmM))
  · intro s hs p t d₀ hp ht hd₀ ih m hm hdm hmM
    have l : d₀ < exsIntro s p t d₀ := by simp
    simp only [fstIdx_exsIntro]
    exact rule_exs hs hp ht (by
      simpa [hd₀.1] using ih m hm (le_trans l.le hdm) (le_trans (add_le_add (le_refl m) l.le) hmM))
  · intro s hs d₀ hsub hd₀ ih m hm hdm hmM
    have l : d₀ < wkRule s d₀ := by simp
    simp only [fstIdx_wkRule]
    exact rule_wk hsub (ih m hm (le_trans l.le hdm) (le_trans (add_le_add (le_refl m) l.le) hmM))
  · intro s hs d₀ he hd₀ ih m hm hdm hmM
    have l : d₀ < shiftRule s d₀ := by simp
    simp only [fstIdx_shiftRule]
    rw [he]
    have hl : d₀ + 1 ≤ shiftRule s d₀ := lt_iff_succ_le.mp l
    refine rule_shift hd₀.isFormulaSet (ih (m + 1) ?_ ?_ ?_)
    · exact le_trans (add_le_add (le_refl m) (le_trans (le_add_of_nonneg_left (by simp)) hl)) hmM
    · exact le_trans (le_trans l.le hdm) (by simp)
    · calc m + 1 + d₀ = m + (d₀ + 1) := by ring
        _ ≤ m + shiftRule s d₀ := add_le_add (le_refl m) hl
        _ ≤ M := hmM
  · intro s hs p d₁ d₂ hd₁ hd₂ ih₁ ih₂ m hm hdm hmM
    have l₁ : d₁ < cutRule s p d₁ d₂ := by simp
    have l₂ : d₂ < cutRule s p d₁ d₂ := by simp
    simp only [fstIdx_cutRule]
    refine rule_cut hd₁.isFormulaSet ?_ ?_
    · simpa [hd₁.1] using ih₁ m hm (le_trans l₁.le hdm) (le_trans (add_le_add (le_refl m) l₁.le) hmM)
    · simpa [hd₂.1] using ih₂ m hm (le_trans l₂.le hdm) (le_trans (add_le_add (le_refl m) l₂.le) hmM)
  · intro s hs p hp hpU m _ _ _
    simpa using rule_axm hp (hU p hpU m)

/-- An internal refutation of `U` gives an internal C proof of the falsity code. -/
theorem refutation_tr (U : Theory ℒₛₑₜ) [U.Δ₁]
    (hU : ∀ p ∈ U.Δ₁Class (V := V), ∀ m, L.T.Prov (chiS m p))
    (h : Bootstrapping.Provable U (^⊥ : V)) : L.Pr 1 := by
  obtain ⟨d, hd⟩ := h
  have hs := derivation_tr L U hU (d + d) hd.2 d (by simp) le_rfl le_rfl
  rw [hd.1] at hs
  have e : L.T.Prov (imp (seqC ({^⊥} : V) d) 1) := seqC_elim L fun r hr => by
    have : r = ^⊥ := by simpa using hr
    subst this
    simp only [chiS, tr_falsum, negPair, pi₁_pair]
    exact L.T.toLogic.dne 1
  exact L.T.mp hs e

end

end ZF209.Internal.Tait
