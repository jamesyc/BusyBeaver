module
public import Halting.Rules
public import ModelCRefutationPhysical
@[expose] public section
/-! # The trace predicate is closed under the machine's rules, and `D(1)` halts

Traces concatenate (`trace_append`, an order induction in the model), so "some trace
contains `x`" is closed under modus ponens; generalization and the axiom templates add one
entry. A trace containing the falsity code `1` makes `1` compilable, and the old halting
chain turns that into physical halting of the literal machine. -/
namespace ZF209.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZF209.MM0ModelReplay ZFR.ArithmeticRepresentation
open ZF209.Internal (imp all codes)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

local instance append_definable_prov : 𝚺ᴬ₁-Function₂ (modelListAppend (M := M)) := appendGraph_defined.to_definable
local instance memberCode_definable_prov : 𝚺ᴬ₁-Function₂ (modelMemberCode (M := M)) := memberCodeGraph_defined.to_definable
local instance trace_definable_prov : 𝚺ᴬ₁-Predicate (modelTrace (cRule (M := M))) := cTrace_defined.to_definable

theorem member_append (x a b : M) :
    modelMember x (modelListAppend a b) ↔ modelMember x a ∨ modelMember x b := by
  have hh : ∀ a : M, modelMemberCode x (modelListAppend a b) = 1 ↔
      modelMemberCode x a = 1 ∨ modelMemberCode x b = 1 := by
    apply ISigma1.sigma1_order_induction
    · definability
    · intro n ih
      by_cases hz : n = 0
      · subst n
        simp [modelListAppend_zero, modelMemberCode_zero]
      have hn := pos_iff_ne_zero.mpr hz
      have he : n = modelListCons (modelListHead n) (modelListTail n) :=
        (modelList_reconstruct n hn).symm
      change modelMember x (modelListAppend n b) ↔ modelMember x n ∨ modelMember x b
      rw [he, modelListAppend_cons, modelMember_cons, modelMember_cons]
      exact (or_congr_right (ih _ (modelListTail_lt n hn))).trans or_assoc.symm
  exact hh a

lemma cRule_append {r a : M} (b : M) (h : cRule r a) : cRule r (modelListAppend a b) := by
  rcases h with h | ⟨c, hc, hi⟩ | ⟨i, c, hc, hr⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨c, (member_append _ _ _).mpr (Or.inl hc),
      (member_append _ _ _).mpr (Or.inl hi)⟩)
  · exact Or.inr (Or.inr ⟨i, c, (member_append _ _ _).mpr (Or.inl hc), hr⟩)

/-- Internal trace concatenation (order induction in the model). -/
theorem trace_append (a b : M) (ha : modelTrace cRule a) (hb : modelTrace cRule b) :
    modelTrace cRule (modelListAppend a b) := by
  have hh : ∀ a : M, modelTrace cRule a → modelTrace cRule (modelListAppend a b) := by
    apply InductionOnHierarchy.order_induction (V := M) 𝚺 2
      (P := fun a => modelTrace cRule a → modelTrace cRule (modelListAppend a b))
    · have h1 : 𝚺ᴬ₁-Predicate (fun a : M => modelTrace cRule a) := by definability
      have h2 : 𝚺ᴬ₁-Predicate (fun a : M => modelTrace cRule (modelListAppend a b)) := by
        definability
      exact Bounding.HierarchySymbol.Definable.imp (h1.of_lt (by decide)) (h2.of_lt (by decide))
    · intro n ih hn
      by_cases hz : n = 0
      · subst n; simpa using hb
      have hp := pos_iff_ne_zero.mpr hz
      have he : n = modelListCons (modelListHead n) (modelListTail n) :=
        (modelList_reconstruct n hp).symm
      rw [he, modelTrace_cons] at hn
      rw [he, modelListAppend_cons, modelTrace_cons]
      exact ⟨ih _ (modelListTail_lt n hp) hn.1, cRule_append _ hn.2⟩
  exact hh a ha

lemma D_iff' (x : M) : D.val.Evalb ![x] ↔ ∃ p, modelTrace cRule p ∧ modelMember x p := by
  rw [D_iff, modelCRule_eq]

lemma D_cons {p : M} (hp : modelTrace cRule p) {r : M} (hr : cRule r p) : D.val.Evalb ![r] :=
  (D_iff' r).mpr ⟨modelListCons r p, (modelTrace_cons _ _ _).mpr ⟨hp, hr⟩,
    (modelMember_cons _ _ _).mpr (Or.inl rfl)⟩

lemma D_ax {r : M} (h : cAxiom r) : D.val.Evalb ![r] := D_cons (modelTrace_zero _) (Or.inl h)

/-- The trace predicate is closed under the machine's rules. -/
theorem provRules : ZF209.Internal.ProvRules D M where
  mp {a b} ha hab := by
    obtain ⟨p, hp, hpa⟩ := (D_iff' a).mp ha
    obtain ⟨q, hq, hqb⟩ := (D_iff' _).mp hab
    exact D_cons (trace_append p q hp hq) (Or.inr (Or.inl ⟨a,
      (member_append _ _ _).mpr (Or.inl hpa), (member_append _ _ _).mpr (Or.inr hqb)⟩))
  gen x {a} ha := by
    obtain ⟨p, hp, hpa⟩ := (D_iff' a).mp ha
    exact D_cons hp (Or.inr (Or.inr ⟨x, a, hpa, rfl⟩))
  h1 d h := D_ax ⟨0, d, h, 0, by simp⟩
  h2 d a h := D_ax ⟨a, d, h, 0, by simp⟩
  h3 h d a := D_ax ⟨a, d, h, 0, by simp⟩
  h4 h d a := D_ax ⟨a, d, h, 0, by simp⟩
  h5 d h := D_ax ⟨0, d, h, 0, by simp⟩
  h6 d a h := D_ax ⟨a, d, h, 0, by simp⟩
  r8 a b c u hu := D_ax ⟨b, a, c, u, by simp [hu]⟩
  gate a b c hca hcb := D_ax ⟨c, b, a, 0, by simp [hca, hcb]⟩

/-- A trace containing the falsity code halts the literal machine. -/
theorem halts_of_D (h : D.val.Evalb ![(1 : M)]) : BinaryTape.physicalHalts (M := M) := by
  obtain ⟨p, hp, h1⟩ := (D_iff 1).mp h
  exact ZF209.NativePhysicalLift.literalCRefutation_physical
    (ZF209.ModelCommands.refutation_compilable p hp h1)

end ZF209.Halting
