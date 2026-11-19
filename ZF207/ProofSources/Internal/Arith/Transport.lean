module
public import Internal.Arith.SubstVar
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic
@[expose] public section
/-! # Transporting internal derivations along the arithmetic translation

`jset s` is the image of a sequent under `J ι 0`. Every internal derivation of a
theory `T` of arithmetic becomes a derivation of a theory `U` of set theory,
provided `U` contains the translations of `T`'s axioms and proves each
existential-introduction step `J (p[t]) → J (∃p)` (`ExStep`). -/
namespace ZF207.Internal.Arith
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

attribute [local instance] Classical.propDecidable

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

/-- A closed `ℒₛₑₜ` term is a free variable, so shifting past a binder fixes it. -/
lemma bs_closed {ε : V} (he : IsSemiterm ℒₛₑₜ 0 ε) : bs ε = ε := by
  rcases set_term_cases.mp he with ⟨z, hz, _⟩ | ⟨x, rfl⟩
  · simp at hz
  · simp [bs]

lemma closed_semiterm {ε : V} (he : IsSemiterm ℒₛₑₜ 0 ε) (n : V) : IsSemiterm ℒₛₑₜ n ε := by
  rcases set_term_cases.mp he with ⟨z, hz, _⟩ | ⟨x, rfl⟩
  · simp at hz
  · simp

lemma subst_closed {ε w : V} (he : IsSemiterm ℒₛₑₜ 0 ε) : termSubst ℒₛₑₜ w ε = ε := by
  rcases set_term_cases.mp he with ⟨z, hz, _⟩ | ⟨x, rfl⟩
  · simp at hz
  · simp

theorem J_free {ε p : V} (he : IsSemiterm ℒₛₑₜ 0 ε) (hp : IsSemiformula ℒₒᵣ 1 p) :
    J ι (termShift ℒₛₑₜ ε) 0 (free ℒₒᵣ p) = free ℒₛₑₜ (J ι ε 1 p) := by
  have hw : IsSemitermVec ℒₒᵣ 1 0 (^&0 ∷ (0 : V)) := by
    rw [show (1 : V) = 0 + 1 by simp]; simp
  have hv : VarVec 1 (^&0 ∷ (0 : V)) := VarVec.of_cases fun i hi => by
    have : i = 0 := by simpa using hi
    subst this; right; exact ⟨0, by simp⟩
  have he' : IsSemiterm ℒₛₑₜ 0 (termShift ℒₛₑₜ ε) := he.termShift
  have h := J_subst ι 1 _ hp.shift _ (closed_semiterm he' 1) 0 _ hw hv
  rw [subst_closed he'] at h
  rw [free, substs1, h, J_shift ι 1 p hp ε (closed_semiterm he 1), free, substs1]

/-! ## Images of sequents -/

/-- The marker template at a term. -/
noncomputable def markAt (ε : V) : V := subst ℒₛₑₜ (ε ∷ 0) (tq ι.mark : V)

lemma markAt_semiformula {m ε : V} (he : IsSemiterm ℒₛₑₜ m ε) :
    IsSemiformula ℒₛₑₜ m (markAt ι ε) := by
  have h1 : IsSemiformula ℒₛₑₜ 1 (tq ι.mark : V) := by simpa using tq_semiformula (V := V) ι.mark
  exact h1.subst (m := m) (by rw [show (1 : V) = 0 + 1 by simp]; simp [he])

lemma shift_markAt {m ε : V} (he : IsSemiterm ℒₛₑₜ m ε) :
    shift ℒₛₑₜ (markAt ι ε) = markAt ι (termShift ℒₛₑₜ ε) := by
  have h1 : IsSemiformula ℒₛₑₜ 1 (tq ι.mark : V) := by simpa using tq_semiformula (V := V) ι.mark
  have hw : IsSemitermVec ℒₛₑₜ 1 m (ε ∷ (0 : V)) := by
    rw [show (1 : V) = 0 + 1 by simp]; simp [he]
  unfold markAt
  rw [shift_substs h1 hw, shift_tq, termShiftVec_cons₁ he.isUTerm]

noncomputable def markAtDef (ι : Interp) : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y e. ∃ w, !adjoinDef w e 0 ∧ !(substsGraph ℒₛₑₜ) y w ↑(tq ι.mark)”

lemma markAt_defined : 𝚺ᴬ₁-Function₁ (markAt ι : V → V) via markAtDef ι := .mk fun v => by
  simp [markAtDef, markAt, subst.defined.iff, numeral_eq_natCast]

instance markAt_definable (Γ m) : Γᴬ_[m + 1]-Function₁ (markAt ι : V → V) :=
  .of_sigmaOne (markAt_defined ι).to_definable

namespace JSet

noncomputable def blueprint (ι : Interp) : PR.Blueprint 2 where
  zero := .mkSigma “y s e. y = 0”
  succ := .mkSigma “y z n s e. (n ∈ s ∧ ∃ j, !(JDef ι) j e 0 n ∧
    !insertDef y j z) ∨ (n ∉ s ∧ y = z)”

noncomputable def construction : PR.Construction V (blueprint ι) where
  zero _ := 0
  succ v n z := if n ∈ v 0 then insert (J ι (v 1) 0 n) z else z
  zero_defined := .mk fun v => by simp [blueprint]
  succ_defined := .mk fun v => by
    by_cases h : v 2 ∈ v 3 <;> simp [blueprint, h, (J_defined ι).iff]

end JSet

/-- The members of `s` below `n`, translated at `ε`. -/
noncomputable def jimgUpTo (ε s n : V) : V := (JSet.construction ι).result ![s, ε] n

/-- The image of a sequent at `ε`. -/
noncomputable def jimg (ε s : V) : V := jimgUpTo ι ε s s

/-- The translated sequent: the image together with `¬ Mark ε`. -/
noncomputable def jset (ε s : V) : V := insert (neg ℒₛₑₜ (markAt ι ε)) (jimg ι ε s)

@[simp] lemma jimgUpTo_zero (ε s : V) : jimgUpTo ι ε s 0 = 0 := by
  simp [jimgUpTo, JSet.construction]

@[simp] lemma jimgUpTo_succ (ε s n : V) :
    jimgUpTo ι ε s (n + 1) =
      if n ∈ s then insert (J ι ε 0 n) (jimgUpTo ι ε s n) else jimgUpTo ι ε s n := by
  simp [jimgUpTo, JSet.construction]

noncomputable def jimgUpToDef (ι : Interp) : 𝚺ᴬ₁.Semisentence 4 := (JSet.blueprint ι).resultDef

instance jimgUpTo_defined : 𝚺ᴬ₁-Function₃ (jimgUpTo ι : V → V → V → V) via
    (jimgUpToDef ι).rew (Rew.subst ![#0, #3, #2, #1]) := .mk fun v => by
  have h := (JSet.construction ι (V := V)).result_defined_iff ![v 0, v 3, v 2, v 1]
  have e : (fun i : Fin 2 => (![v 0, v 3, v 2, v 1] : Fin 4 → V) i.succ.succ) = ![v 2, v 1] := by
    funext i; match i with | 0 => rfl | 1 => rfl
  simp only [jimgUpToDef, Bounding.HierarchySymbol.Semiformula.val_rew, Semiformula.eval_rew,
    Function.comp_def]
  simpa [jimgUpTo, e, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using h

instance jimgUpTo_definable (Γ m) : Γᴬ_[m + 1]-Function₃ (jimgUpTo ι : V → V → V → V) :=
  .of_sigmaOne (jimgUpTo_defined ι).to_definable

lemma mem_jimgUpTo (ε s : V) : ∀ n y : V, y ∈ jimgUpTo ι ε s n ↔ ∃ p < n, p ∈ s ∧ y = J ι ε 0 p := by
  intro n
  induction n using ISigma1.pi1_succ_induction
  · definability
  · simp
  · rename_i n ih
    intro y
    rw [jimgUpTo_succ]
    constructor
    · intro hy
      split at hy
      · rcases mem_bitInsert_iff.mp hy with rfl | hy
        · exact ⟨n, by simp, by assumption, rfl⟩
        · obtain ⟨p, hp, hps, rfl⟩ := (ih y).mp hy
          exact ⟨p, lt_trans hp (by simp), hps, rfl⟩
      · obtain ⟨p, hp, hps, rfl⟩ := (ih y).mp hy
        exact ⟨p, lt_trans hp (by simp), hps, rfl⟩
    · rintro ⟨p, hp, hps, rfl⟩
      rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hp) with hp | rfl
      · have := (ih (J ι ε 0 p)).mpr ⟨p, hp, hps, rfl⟩
        split
        · exact mem_bitInsert_iff.mpr (Or.inr this)
        · exact this
      · simp only [hps, ite_true]; exact mem_bitInsert_iff.mpr (Or.inl rfl)

lemma mem_jimg {ε s y : V} : y ∈ jimg ι ε s ↔ ∃ p ∈ s, y = J ι ε 0 p := by
  rw [jimg, mem_jimgUpTo]
  constructor
  · rintro ⟨p, _, hps, rfl⟩; exact ⟨p, hps, rfl⟩
  · rintro ⟨p, hps, rfl⟩; exact ⟨p, lt_of_mem hps, hps, rfl⟩

lemma mem_jset {ε s y : V} :
    y ∈ jset ι ε s ↔ y = neg ℒₛₑₜ (markAt ι ε) ∨ ∃ p ∈ s, y = J ι ε 0 p := by
  rw [jset, mem_bitInsert_iff, mem_jimg]

lemma J_mem_jset {ε s p : V} (h : p ∈ s) : J ι ε 0 p ∈ jset ι ε s :=
  (mem_jset ι).mpr (Or.inr ⟨p, h, rfl⟩)

lemma mark_mem_jset (ε s : V) : neg ℒₛₑₜ (markAt ι ε) ∈ jset ι ε s :=
  (mem_jset ι).mpr (Or.inl rfl)

lemma jset_formulaSet {ε s : V} (he : IsSemiterm ℒₛₑₜ 0 ε) (hs : IsFormulaSet ℒₒᵣ s) :
    IsFormulaSet ℒₛₑₜ (jset ι ε s) := by
  intro y hy
  rcases (mem_jset ι).mp hy with rfl | ⟨p, hp, rfl⟩
  · exact IsSemiformula.neg_iff.mpr (markAt_semiformula ι he)
  · exact J_semiformula ι 0 p (hs p hp) ε he

lemma jset_insert {ε p s : V} :
    ∀ y, y ∈ jset ι ε (insert p s) ↔ y ∈ insert (J ι ε 0 p) (jset ι ε s) := by
  intro y
  rw [mem_jset, mem_bitInsert_iff, mem_jset]
  constructor
  · rintro (rfl | ⟨q, hq, rfl⟩)
    · exact Or.inr (Or.inl rfl)
    · rcases mem_bitInsert_iff.mp hq with rfl | hq
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨q, hq, rfl⟩)
  · rintro (rfl | rfl | ⟨q, hq, rfl⟩)
    · exact Or.inr ⟨p, mem_bitInsert_iff.mpr (Or.inl rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨q, mem_bitInsert_iff.mpr (Or.inr hq), rfl⟩

lemma jset_setShift {ε s : V} (he : IsSemiterm ℒₛₑₜ 0 ε) (hs : IsFormulaSet ℒₒᵣ s) :
    ∀ y, y ∈ jset ι (termShift ℒₛₑₜ ε) (setShift ℒₒᵣ s) ↔ y ∈ setShift ℒₛₑₜ (jset ι ε s) := by
  intro y
  rw [mem_jset, mem_setShift_iff]
  have hm := markAt_semiformula ι he
  constructor
  · rintro (rfl | ⟨q, hq, rfl⟩)
    · exact ⟨neg ℒₛₑₜ (markAt ι ε), mark_mem_jset ι ε s, by rw [shift_neg hm, shift_markAt ι he]⟩
    · obtain ⟨p, hp, rfl⟩ := mem_setShift_iff.mp hq
      exact ⟨J ι ε 0 p, J_mem_jset ι hp, J_shift ι 0 p (hs p hp) ε he⟩
  · rintro ⟨x, hx, rfl⟩
    rcases (mem_jset ι).mp hx with rfl | ⟨p, hp, rfl⟩
    · exact Or.inl (by rw [shift_neg hm, shift_markAt ι he])
    · exact Or.inr ⟨shift ℒₒᵣ p, shift_mem_setShift hp, (J_shift ι 0 p (hs p hp) ε he).symm⟩

lemma jset_mono {ε s s' : V} (h : s' ⊆ s) : jset ι ε s' ⊆ jset ι ε s := by
  intro y hy
  rcases (mem_jset ι).mp hy with rfl | ⟨p, hp, rfl⟩
  · exact mark_mem_jset ι ε s
  · exact J_mem_jset ι (h hp)

lemma jset_defined : 𝚺ᴬ₁-Function₂ (jset ι : V → V → V) := by
  have : 𝚺ᴬ₁-Function₂ (fun ε s : V => jimgUpTo ι ε s s) := by definability
  unfold jset jimg; definability

instance jset_definable (Γ m) : Γᴬ_[m + 1]-Function₂ (jset ι : V → V → V) :=
  .of_sigmaOne (jset_defined ι)

/-! ## Induction on derivations in models of PA -/

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

/-- `Derivation.induction1` for Π2 predicates. -/
theorem derivation_induction (P : V → Prop) (hP : 𝚷ᴬ_[1 + 1]-Predicate P)
    {d} (hd : Derivation T d)
    (hAxL : ∀ s, IsFormulaSet L s → ∀ p ∈ s, neg L p ∈ s → P (axL s p))
    (hVerumIntro : ∀ s, IsFormulaSet L s → ^⊤ ∈ s → P (verumIntro s))
    (hAnd : ∀ s, IsFormulaSet L s → ∀ p q dp dq, p ^⋏ q ∈ s →
      DerivationOf T dp (insert p s) → DerivationOf T dq (insert q s) →
      P dp → P dq → P (andIntro s p q dp dq))
    (hOr : ∀ s, IsFormulaSet L s → ∀ p q d, p ^⋎ q ∈ s → DerivationOf T d (insert p (insert q s)) →
      P d → P (orIntro s p q d))
    (hAll : ∀ s, IsFormulaSet L s → ∀ p d, ^∀ p ∈ s →
      DerivationOf T d (insert (free L p) (setShift L s)) →
      P d → P (allIntro s p d))
    (hExs : ∀ s, IsFormulaSet L s → ∀ p t d, ^∃ p ∈ s → IsTerm L t →
      DerivationOf T d (insert (substs1 L t p) s) →
      P d → P (exsIntro s p t d))
    (hWk : ∀ s, IsFormulaSet L s → ∀ d, fstIdx d ⊆ s → Derivation T d →
      P d → P (wkRule s d))
    (hShift : ∀ s, IsFormulaSet L s → ∀ d, s = setShift L (fstIdx d) → Derivation T d →
      P d → P (shiftRule s d))
    (hCut : ∀ s, IsFormulaSet L s → ∀ p d₁ d₂, DerivationOf T d₁ (insert p s) →
      DerivationOf T d₂ (insert (neg L p) s) →
      P d₁ → P d₂ → P (cutRule s p d₁ d₂))
    (hRoot : ∀ s, IsFormulaSet L s → ∀ p, p ∈ s → p ∈ T.Δ₁Class → P (axm s p)) : P d := by
  have key : ∀ d : V, Derivation T d → P d := by
    refine InductionOnHierarchy.order_induction_sigma 𝚷 (1 + 1)
      (P := fun d => Derivation T d → P d)
      (.imp (Derivation.definable' (T := T) (Γ := 𝚺) (m := 1)) hP) ?_
    intro d ih hd
    rcases hd.case with ⟨hds,
      (⟨s, p, rfl, hps, hnps⟩ | ⟨s, rfl, hs⟩ |
        ⟨s, p, q, dp, dq, rfl, hpq, h₁, h₂⟩ | ⟨s, p, q, d, rfl, hpq, h⟩ |
        ⟨s, p, d, rfl, hp, h⟩ | ⟨s, p, t, d, rfl, hp, ht, h⟩ |
        ⟨s, d, rfl, h, hC⟩ | ⟨s, d, rfl, h, hC⟩ |
        ⟨s, p, d₁, d₂, rfl, h₁, h₂⟩ | ⟨s, p, rfl, hs, hT⟩)⟩
    · exact hAxL s (by simpa using hds) p hps hnps
    · exact hVerumIntro s (by simpa using hds) hs
    · exact hAnd s (by simpa using hds) p q dp dq hpq h₁ h₂ (ih dp (by simp) h₁.2)
        (ih dq (by simp) h₂.2)
    · exact hOr s (by simpa using hds) p q d hpq h (ih d (by simp) h.2)
    · exact hAll s (by simpa using hds) p d hp h (ih d (by simp) h.2)
    · exact hExs s (by simpa using hds) p t d hp ht h (ih d (by simp) h.2)
    · exact hWk s (by simpa using hds) d h hC (ih d (by simp) hC)
    · exact hShift s (by simpa using hds) d h hC (ih d (by simp) hC)
    · exact hCut s (by simpa using hds) p d₁ d₂ h₁ h₂ (ih d₁ (by simp) h₁.2)
        (ih d₂ (by simp) h₂.2)
    · exact hRoot s (by simpa using hds) p hs hT
  exact key d hd

end

/-! ## The transport -/

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (ι : Interp)

/-- `U` proves each translated existential-introduction step. -/
def ExStep (U : Theory ℒₛₑₜ) [U.Δ₁] (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Prop :=
  ∀ ε p t : V, IsSemiterm ℒₛₑₜ 0 ε → IsSemiformula ℒₒᵣ 1 p → IsTerm ℒₒᵣ t →
    Derivable U (insert (neg ℒₛₑₜ (J ι ε 0 (substs1 ℒₒᵣ t p))) (insert (J ι ε 0 (^∃ p)) (0 : V)))

/-- `U` derives each translated axiom of `T` from the marker hypothesis. -/
def AxStep (T : ArithmeticTheory) [T.Δ₁] (U : Theory ℒₛₑₜ) [U.Δ₁] (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Prop :=
  ∀ p ∈ T.Δ₁Class (V := V), ∀ ε, IsSemiterm ℒₛₑₜ 0 ε →
    Derivable U (insert (neg ℒₛₑₜ (markAt ι ε)) (insert (J ι ε 0 p) (0 : V)))

lemma insert_sub {a b s : V} (ha : a ∈ s) (hb : b ∈ s) : insert a (insert b (0 : V)) ⊆ s := by
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · exact ha
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · exact hb
  · simp at hy

lemma fv_closed (x : V) : IsSemiterm ℒₛₑₜ 0 (^&x : V) := by simp

/-- Translated derivations. The marker is a free variable `&x` with `x` at least the
derivation code: the `∀`-rule moves it to `&(x+1)`, the shift rule to `&(x-1)`. -/
theorem derivation_jset (T : ArithmeticTheory) [T.Δ₁] (U : Theory ℒₛₑₜ) [U.Δ₁]
    (hT : AxStep ι T U V) (hex : ExStep ι U V) {d : V} (hd : Derivation T d) :
    ∀ x, d ≤ x → Derivable U (jset ι (^&x) (fstIdx d)) := by
  have hD : 𝚷ᴬ_[1 + 1]-Predicate (fun d : V => ∀ x, d ≤ x → Derivable U (jset ι (^&x) (fstIdx d))) := by
    have : 𝚷ᴬ_[1 + 1]-Predicate (Derivable (V := V) U) := .of_lt Derivable.definable (by simp)
    have : 𝚷ᴬ_[1 + 1]-Function₂ (jset ι : V → V → V) := inferInstance
    definability
  refine derivation_induction (T := T)
    (fun d => ∀ x, d ≤ x → Derivable U (jset ι (^&x) (fstIdx d))) hD hd
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s hs p hp hn x _
    simp only [fstIdx_axL]
    refine Derivable.em (jset_formulaSet ι (fv_closed x) hs) (J ι (^&x) 0 p) (J_mem_jset ι hp) ?_
    rw [← J_neg ι 0 p (hs p hp) _ (fv_closed x)]; exact J_mem_jset ι hn
  · intro s hs h x _
    simp only [fstIdx_verumIntro]
    exact Derivable.verum (jset_formulaSet ι (fv_closed x) hs)
      (by simpa using J_mem_jset ι (ε := ^&x) h)
  · intro s hs p q dp dq hpq hdp hdq ihp ihq x hx
    have hpq' := IsSemiformula.and.mp (hs _ hpq)
    simp only [fstIdx_andIntro]
    refine Derivable.and_m (p := J ι (^&x) 0 p) (q := J ι (^&x) 0 q) ?_ ?_ ?_
    · simpa [J_and hpq'.1.isUFormula hpq'.2.isUFormula] using J_mem_jset ι (ε := ^&x) hpq
    · exact Derivable.ofSetEq (jset_insert ι)
        (by simpa [hdp.1] using ihp x (le_trans (le_of_lt (by simp)) hx))
    · exact Derivable.ofSetEq (jset_insert ι)
        (by simpa [hdq.1] using ihq x (le_trans (le_of_lt (by simp)) hx))
  · intro s hs p q d₀ hpq hd₀ ih x hx
    have hpq' := IsSemiformula.or.mp (hs _ hpq)
    simp only [fstIdx_orIntro]
    refine Derivable.or_m (p := J ι (^&x) 0 p) (q := J ι (^&x) 0 q) ?_ ?_
    · simpa [J_or hpq'.1.isUFormula hpq'.2.isUFormula] using J_mem_jset ι (ε := ^&x) hpq
    · refine Derivable.ofSetEq (fun y => ?_)
        (by simpa [hd₀.1] using ih x (le_trans (le_of_lt (by simp)) hx))
      rw [jset_insert ι, mem_bitInsert_iff, mem_bitInsert_iff, mem_bitInsert_iff, jset_insert ι,
        mem_bitInsert_iff]
  · intro s hs p d₀ hp hd₀ ih x hx
    have he := fv_closed (V := V) x
    have hp1 : IsSemiformula ℒₒᵣ 1 p := by simpa using hs _ hp
    simp only [fstIdx_allIntro]
    have he1 := closed_semiterm he 1
    have hd : IsSemiformula ℒₛₑₜ 1 (un (tq ι.dom) (^&x) ^#0) :=
      un_semiformula ι.dom he1 (by simp)
    have hj : IsSemiformula ℒₛₑₜ 1 (J ι (^&x) 1 p) := J_semiformula ι 1 p hp1 _ he1
    refine Derivable.all_m (p := neg ℒₛₑₜ (un (tq ι.dom) (^&x) ^#0) ^⋎ J ι (^&x) 1 p) ?_ ?_
    · simpa [J_all hp1.isUFormula, bs_closed he] using J_mem_jset ι (ε := ^&x) hp
    · have hih := ih (x + 1) (le_trans (le_of_lt (by simp)) (le_trans hx (by simp)))
      have hss : ∀ y, y ∈ jset ι (^&(x + 1)) (setShift ℒₒᵣ s) ↔
          y ∈ setShift ℒₛₑₜ (jset ι (^&x) s) := by simpa using jset_setShift ι he hs
      have hjf : J ι (^&(x + 1)) 0 (free ℒₒᵣ p) = free ℒₛₑₜ (J ι (^&x) 1 p) := by
        simpa using J_free ι he hp1
      have h₀ : Derivable U (insert (free ℒₛₑₜ (J ι (^&x) 1 p))
          (setShift ℒₛₑₜ (jset ι (^&x) s))) := by
        refine Derivable.ofSetEq (fun y => ?_) (by simpa [hd₀.1] using hih)
        rw [jset_insert ι, mem_bitInsert_iff, mem_bitInsert_iff, hss, hjf]
      have hfo : free ℒₛₑₜ (neg ℒₛₑₜ (un (tq ι.dom) (^&x) ^#0) ^⋎ J ι (^&x) 1 p) =
          free ℒₛₑₜ (neg ℒₛₑₜ (un (tq ι.dom) (^&x) ^#0)) ^⋎ free ℒₛₑₜ (J ι (^&x) 1 p) := by
        simp [free, substs1, hd.isUFormula, hj.isUFormula, hd.shift.isUFormula,
          hj.shift.isUFormula]
      rw [hfo]
      have hF : IsFormulaSet ℒₛₑₜ (insert (free ℒₛₑₜ (neg ℒₛₑₜ (un (tq ι.dom) (^&x) ^#0)))
          (insert (free ℒₛₑₜ (J ι (^&x) 1 p)) (setShift ℒₛₑₜ (jset ι (^&x) s)))) := by
        intro y hy
        rcases mem_bitInsert_iff.mp hy with rfl | hy
        · exact (IsSemiformula.neg_iff.mpr hd).free
        rcases mem_bitInsert_iff.mp hy with rfl | hy
        · exact hj.free
        · exact (jset_formulaSet ι he hs).setShift y hy
      refine Derivable.or (Derivable.wk hF ?_ h₀)
      intro y hy
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inl rfl)))
      · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr hy)))
  · intro s hs p t d₀ hp ht hd₀ ih x hx
    have he := fv_closed (V := V) x
    have hp1 : IsSemiformula ℒₒᵣ 1 p := by simpa using hs _ hp
    simp only [fstIdx_exsIntro]
    have hX : IsFormula ℒₛₑₜ (J ι (^&x) 0 (substs1 ℒₒᵣ t p)) :=
      J_semiformula ι 0 _ (IsSemiformula.substs1 ht hp1) _ he
    have h₁ : Derivable U (insert (J ι (^&x) 0 (substs1 ℒₒᵣ t p)) (jset ι (^&x) s)) :=
      Derivable.ofSetEq (jset_insert ι)
        (by simpa [hd₀.1] using ih x (le_trans (le_of_lt (by simp)) hx))
    have hF : IsFormulaSet ℒₛₑₜ
        (insert (neg ℒₛₑₜ (J ι (^&x) 0 (substs1 ℒₒᵣ t p))) (jset ι (^&x) s)) := by
      intro y hy
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · exact IsSemiformula.neg_iff.mpr hX
      · exact jset_formulaSet ι he hs y hy
    refine Derivable.cut (J ι (^&x) 0 (substs1 ℒₒᵣ t p)) h₁
      (Derivable.wk hF ?_ (hex _ p t he hp1 ht))
    intro y hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · exact mem_bitInsert_iff.mpr (Or.inl rfl)
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · exact mem_bitInsert_iff.mpr (Or.inr (J_mem_jset ι hp))
    · simp at hy
  · intro s hs d₀ hsub hd₀ ih x hx
    simp only [fstIdx_wkRule]
    exact Derivable.wk (jset_formulaSet ι (fv_closed x) hs) (jset_mono ι hsub)
      (ih x (le_trans (le_of_lt (by simp)) hx))
  · intro s hs d₀ hsh hd₀ ih x hx
    simp only [fstIdx_shiftRule]
    rw [hsh]
    have hpos : d₀ < x := lt_of_lt_of_le (by simp) hx
    rcases zero_or_succ x with rfl | ⟨x', rfl⟩
    · simp at hpos
    have hx' : d₀ ≤ x' := le_iff_lt_succ.mpr hpos
    have := Derivable.shift (ih x' hx')
    have hss : ∀ y, y ∈ jset ι (^&(x' + 1)) (setShift ℒₒᵣ (fstIdx d₀)) ↔
        y ∈ setShift ℒₛₑₜ (jset ι (^&x') (fstIdx d₀)) := by
      simpa using jset_setShift ι (fv_closed x') hd₀.isFormulaSet
    exact Derivable.ofSetEq (fun y => (hss y).symm) this
  · intro s hs p d₁ d₂ hd₁ hd₂ ih₁ ih₂ x hx
    have he := fv_closed (V := V) x
    simp only [fstIdx_cutRule]
    have hp : IsFormula ℒₒᵣ p := hd₁.isFormulaSet p (mem_bitInsert_iff.mpr (Or.inl rfl))
    refine Derivable.cut (J ι (^&x) 0 p) (Derivable.ofSetEq (jset_insert ι)
      (by simpa [hd₁.1] using ih₁ x (le_trans (le_of_lt (by simp)) hx))) ?_
    rw [← J_neg ι 0 p hp _ he]
    exact Derivable.ofSetEq (jset_insert ι)
      (by simpa [hd₂.1] using ih₂ x (le_trans (le_of_lt (by simp)) hx))
  · intro s hs p hp hpT x _
    simp only [fstIdx_axm]
    exact Derivable.wk (jset_formulaSet ι (fv_closed x) hs)
      (insert_sub (mark_mem_jset ι _ s) (J_mem_jset ι hp)) (hT p hpT _ (fv_closed x))

/-- An internal refutation of `T` gives a `U`-derivation of `¬ Mark &x` for some `x`. -/
theorem refutation_jset (T : ArithmeticTheory) [T.Δ₁] (U : Theory ℒₛₑₜ) [U.Δ₁]
    (hT : AxStep ι T U V) (hex : ExStep ι U V) (h : Bootstrapping.Provable T (^⊥ : V)) :
    ∃ x : V, Derivable U (insert (neg ℒₛₑₜ (markAt ι (^&x))) (0 : V)) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, ?_⟩
  have h₁ := derivation_jset ι T U hT hex hd.2 d le_rfl
  rw [hd.1] at h₁
  have hm : IsFormula ℒₛₑₜ (neg ℒₛₑₜ (markAt ι (^&d))) :=
    IsSemiformula.neg_iff.mpr (markAt_semiformula ι (fv_closed d))
  have hS : IsFormulaSet ℒₛₑₜ (insert (neg ℒₛₑₜ (markAt ι (^&d))) (0 : V)) := by
    intro y hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · exact hm
    · simp at hy
  have h₂ : Derivable U (insert (^⊥ : V) (insert (neg ℒₛₑₜ (markAt ι (^&d))) (0 : V))) := by
    refine Derivable.ofSetEq (fun y => ?_) h₁
    rw [mem_jset, mem_bitInsert_iff, mem_bitInsert_iff]
    simp only [mem_singleton_iff, exists_eq_left, J_falsum]
    constructor
    · rintro (h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · rintro (h | h | h)
      · exact Or.inr h
      · exact Or.inl h
      · simp at h
  have h₃ : Derivable U (insert (neg ℒₛₑₜ (^⊥ : V)) (insert (neg ℒₛₑₜ (markAt ι (^&d))) (0 : V))) :=
    Derivable.verum (by
      intro y hy
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · simp
      · exact hS y hy) (by simp)
  exact Derivable.cut (^⊥ : V) h₂ h₃

end

end ZF207.Internal.Arith
