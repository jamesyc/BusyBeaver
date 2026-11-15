module
public import Halting.Rules
@[expose] public section
/-! # The trace check is Δ1

The rule `cRule` has unbounded witnesses, but each is below the entry it explains: the
parameters of an axiom template are below the template (codes dominate their arguments),
the minor premise of modus ponens is a trace entry (entries are below the list), and the
body and label of a generalization are below it. With these bounds the rule, and the trace
condition built from total Σ1 functions, have Σ1 and Π1 definitions that agree in every
model of `𝗜𝚺₁`. -/
namespace ZF209.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZFR.ArithmeticRepresentation
open ZF209.Internal (imp mem eqc all codes cantor impDef memDef eqcDef allDef negDef exDef
  cneg cex le_cantor_left le_cantor_right le_four_mul)

section
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Codes dominate their arguments -/

lemma le_imp_l {x a : M} (b : M) (h : x ≤ a) : x ≤ imp a b :=
  le_trans h (ZF209.Internal.left_le_imp a b)
lemma le_imp_r {x b : M} (a : M) (h : x ≤ b) : x ≤ imp a b :=
  le_trans h (ZF209.Internal.right_le_imp a b)
lemma le_tag (c t : M) : c ≤ 4 * c + t := le_trans (le_four_mul c) (by simp)
lemma le_all_l {y x : M} (a : M) (h : y ≤ x) : y ≤ all x a :=
  le_trans h (le_trans (le_cantor_right a x) (le_tag _ 2))
lemma le_all_r {y a : M} (x : M) (h : y ≤ a) : y ≤ all x a :=
  le_trans h (le_trans (le_cantor_left a x) (le_tag _ 2))
lemma le_mem_l {y a : M} (b : M) (h : y ≤ a) : y ≤ mem a b :=
  le_trans h (le_trans (le_cantor_left a b) (le_tag _ 1))
lemma le_mem_r {y b : M} (a : M) (h : y ≤ b) : y ≤ mem a b :=
  le_trans h (le_trans (le_cantor_right a b) (le_tag _ 1))
lemma le_eqc_l {y a : M} (b : M) (h : y ≤ a) : y ≤ eqc a b :=
  le_trans h (le_trans (le_cantor_left a b) (le_tag _ 3))
lemma le_eqc_r {y b : M} (a : M) (h : y ≤ b) : y ≤ eqc a b :=
  le_trans h (le_trans (le_cantor_right a b) (le_tag _ 3))

local instance memberCode_definable_delta : 𝚺ᴬ₁-Function₂ (modelMemberCode (M := M)) := memberCodeGraph_defined.to_definable

/-- Trace entries are below the trace. -/
lemma member_lt {b : M} : ∀ xs : M, modelMember b xs → b < xs := by
  have h : ∀ xs : M, modelMemberCode b xs = 1 → b < xs := by
    apply ISigma1.sigma1_order_induction
    · definability
    · intro n ih hn
      by_cases hz : n = 0
      · subst n; simp [modelMemberCode_zero] at hn
      have hp := pos_iff_ne_zero.mpr hz
      have he : n = modelListCons (modelListHead n) (modelListTail n) :=
        (modelList_reconstruct n hp).symm
      change modelMember b n at hn
      rw [he, modelMember_cons] at hn
      rcases hn with hb | hb
      · rw [← hb]; exact modelListHead_lt n hp
      · exact lt_trans (ih _ (modelListTail_lt n hp) hb) (modelListTail_lt n hp)
  exact h

/-! ## The bounded rule -/

local macro "bnd" : tactic => `(tactic| solve_by_elim (maxDepth := 16) [le_imp_l, le_imp_r,
  le_all_l, le_all_r, le_mem_l, le_mem_r, le_eqc_l, le_eqc_r, le_refl])

/-- The axiom templates with parameters below the template. -/
lemma cAxiom_iff_bounded (n : M) : cAxiom n ↔ ∃ a ≤ n, ∃ d ≤ n, ∃ h ≤ n, ∃ u ≤ n,
    n = 0 ∨ n = (codes (V := M)).head6 d a h ∨ n = (codes (V := M)).head5 d h ∨
    n = (codes (V := M)).head4 h d a ∨ n = (codes (V := M)).head3 h d a ∨
    n = (codes (V := M)).head2 d a h ∨ n = (codes (V := M)).head1 d h ∨
    (u ≤ d ∧ n = (codes (V := M)).rho8 d a h u) ∨
    (a ≠ d ∧ a ≠ h ∧ n = (codes (V := M)).bundle h d a) := by
  constructor
  · rintro ⟨a, d, h, u, H⟩
    simp only [CKernel.Generic.Codes.head1, CKernel.Generic.Codes.head2,
      CKernel.Generic.Codes.head3, CKernel.Generic.Codes.head4, CKernel.Generic.Codes.head5,
      CKernel.Generic.Codes.head6, CKernel.Generic.Codes.rho8, CKernel.Generic.Codes.bundle,
      CKernel.Generic.Codes.ex, CKernel.Generic.Codes.neg, CKernel.Generic.Codes.eqVac,
      CKernel.Generic.Codes.memVac, CKernel.Generic.Codes.qGate, codes] at H ⊢
    rcases H with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨hu, rfl⟩ | ⟨hd, hh, rfl⟩
    · exact ⟨0, le_rfl, 0, le_rfl, 0, le_rfl, 0, le_rfl, Or.inl rfl⟩
    · exact ⟨a, by bnd, d, by bnd, h, by bnd, 0, zero_le, Or.inr (Or.inl rfl)⟩
    · exact ⟨0, zero_le, d, by bnd, h, by bnd, 0, zero_le, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨a, by bnd, d, by bnd, h, by bnd, 0, zero_le, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · exact ⟨a, by bnd, d, by bnd, h, by bnd, 0, zero_le, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
    · exact ⟨a, by bnd, d, by bnd, h, by bnd, 0, zero_le, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
    · exact ⟨0, zero_le, d, by bnd, h, by bnd, 0, zero_le, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩
    · exact ⟨a, by bnd, d, by bnd, h, by bnd, u, le_trans hu (by bnd), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, rfl⟩)))))))⟩
    · exact ⟨a, by bnd, d, by bnd, h, by bnd, 0, zero_le, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hd, hh, rfl⟩))))))))⟩
  · rintro ⟨a, -, d, -, h, -, u, -, H⟩
    exact ⟨a, d, h, u, H⟩

lemma cRule_iff_bounded (r xs : M) : cRule r xs ↔ cAxiom r ∨
    (∃ b < xs, modelMember b xs ∧ modelMember (imp b r) xs) ∨
    (∃ i ≤ r, ∃ b ≤ r, modelMember b xs ∧ r = all i b) := by
  unfold cRule
  constructor
  · rintro (h | ⟨b, hb, hi⟩ | ⟨i, b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨b, member_lt _ hb, hb, hi⟩)
    · exact Or.inr (Or.inr ⟨i, le_all_l _ le_rfl, b, le_all_r _ le_rfl, hb, rfl⟩)
  · rintro (h | ⟨b, -, hb, hi⟩ | ⟨i, -, b, -, hb, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨b, hb, hi⟩)
    · exact Or.inr (Or.inr ⟨i, b, hb, h⟩)

end

/-! ## Δ1 definitions -/

def memberΔ : 𝚫ᴬ₁.Semisentence 2 := .mkDelta
  (.mkSigma “x n. ∃ c, !memberCodeGraph c x n ∧ c = 1”)
  (.mkPi “x n. ∀ c, !memberCodeGraph c x n → c = 1”)

def cAxiomΔ : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “n. ∃ a <⁺ n, ∃ d <⁺ n, ∃ h <⁺ n, ∃ u <⁺ n, n = 0 ∨ !head6Def n d a h ∨
    !head5Def n d h ∨ !head4Def n h d a ∨ !head3Def n h d a ∨ !head2Def n d a h ∨
    !head1Def n d h ∨
    (u ≤ d ∧ ∃ p, !impDef p h u ∧ ∃ q, !impDef q p d ∧ ∃ r, !impDef r d h ∧
      ∃ s, !impDef s a h ∧ ∃ t, !impDef t r s ∧ !impDef n q t) ∨
    (a ≠ d ∧ a ≠ h ∧ !bundleDef n h d a)”)
  (.mkPi “n. ∃ a <⁺ n, ∃ d <⁺ n, ∃ h <⁺ n, ∃ u <⁺ n, n = 0 ∨
    (∀ y, !head6Def y d a h → n = y) ∨ (∀ y, !head5Def y d h → n = y) ∨
    (∀ y, !head4Def y h d a → n = y) ∨ (∀ y, !head3Def y h d a → n = y) ∨
    (∀ y, !head2Def y d a h → n = y) ∨ (∀ y, !head1Def y d h → n = y) ∨
    (u ≤ d ∧ ∀ p, !impDef p h u → ∀ q, !impDef q p d → ∀ r, !impDef r d h →
      ∀ s, !impDef s a h → ∀ t, !impDef t r s → !impDef n q t) ∨
    (a ≠ d ∧ a ≠ h ∧ ∀ y, !bundleDef y h d a → n = y)”)

def cRuleΔ : 𝚫ᴬ₁.Semisentence 2 := .mkDelta
  (.mkSigma “r xs. !cAxiomΔ.sigma r ∨
    (∃ b < xs, !memberΔ.sigma b xs ∧ ∃ c, !impDef c b r ∧ !memberΔ.sigma c xs) ∨
    (∃ i <⁺ r, ∃ b <⁺ r, !memberΔ.sigma b xs ∧ !allDef r i b)”)
  (.mkPi “r xs. !cAxiomΔ.pi r ∨
    (∃ b < xs, !memberΔ.pi b xs ∧ ∀ c, !impDef c b r → !memberΔ.pi c xs) ∨
    (∃ i <⁺ r, ∃ b <⁺ r, !memberΔ.pi b xs ∧ !allDef r i b)”)

/-- `n` is a `cRule`-trace. -/
def cTraceΔ : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “n. !tailIterationGraph 0 n n ∧ ∀ k < n, ∃ g, !tailIterationGraph g k n ∧
    (g = 0 ∨ ∃ a, ∃ b, !listHeadGraph a g ∧ !listTailGraph b g ∧ !cRuleΔ.sigma a b)”)
  (.mkPi “n. (∀ z, !tailIterationGraph z n n → z = 0) ∧ ∀ k < n, ∀ g,
    !tailIterationGraph g k n →
    (g = 0 ∨ ∀ a, !listHeadGraph a g → ∀ b, !listTailGraph b g → !cRuleΔ.pi a b)”)

section
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance memberΔ_defined : 𝚫ᴬ₁-Relation (modelMember (M := M)) via memberΔ := .mk <| by
  constructor
  · intro v; simp [memberΔ, Bounding.HierarchySymbol.Semiformula.val_sigma,
      memberCodeGraph_defined.iff]
  · intro v; simp [memberΔ, Bounding.HierarchySymbol.Semiformula.val_sigma,
      memberCodeGraph_defined.iff, modelMember]

instance cAxiomΔ_defined : 𝚫ᴬ₁-Predicate (cAxiom (M := M)) via cAxiomΔ := .mk <| by
  constructor
  · intro v; simp [cAxiomΔ, Bounding.HierarchySymbol.Semiformula.val_sigma, head1Def_iff,
      head2Def_iff, head3Def_iff, head4Def_iff, head5Def_iff, head6Def_iff, bundleDef_iff]
  · intro v; simp [cAxiomΔ, Bounding.HierarchySymbol.Semiformula.val_sigma, head1Def_iff,
      head2Def_iff, head3Def_iff, head4Def_iff, head5Def_iff, head6Def_iff, bundleDef_iff,
      cAxiom_iff_bounded, CKernel.Generic.Codes.rho8, codes]

instance cRuleΔ_defined : 𝚫ᴬ₁-Relation (cRule (M := M)) via cRuleΔ := .mk <| by
  constructor
  · intro v; simp [cRuleΔ, Bounding.HierarchySymbol.Semiformula.val_sigma]
  · intro v; simp [cRuleΔ, Bounding.HierarchySymbol.Semiformula.val_sigma, cRule_iff_bounded]

instance cTraceΔ_defined : 𝚫ᴬ₁-Predicate (modelTrace (cRule (M := M))) via cTraceΔ := .mk <| by
  constructor
  · intro v; simp [cTraceΔ, Bounding.HierarchySymbol.Semiformula.val_sigma,
      tailIterationGraph_defined.iff, ruleHead_defined.iff, ruleTail_defined.iff, eq_comm]
  · intro v; simp [cTraceΔ, Bounding.HierarchySymbol.Semiformula.val_sigma, modelTrace,
      tailIterationGraph_defined.iff, ruleHead_defined.iff, ruleTail_defined.iff, eq_comm]

end

end ZF209.Halting
