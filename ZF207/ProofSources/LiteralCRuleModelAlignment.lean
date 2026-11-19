module
public import ModelReplay4732
public import LiteralMemberModelAlignment
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Exact finite C axiom templates, with all parameters ranging over the PA model. -/
noncomputable def modelCAxiom (n : M) : Prop := ∃ a d h u : M,
 n = 0 ∨ n = t323 a d h ∨ n = t324 a d h ∨ n = t325 a d h ∨
 n = t326 a d h ∨ n = t327 a d h ∨ n = t328 a d h ∨
 (u ≤ d ∧ n = t329 a d h u) ∨ (a ≠ d ∧ a ≠ h ∧ n = t330 a d h)
noncomputable def modelCRule (r xs : M) : Prop :=
 modelCAxiom r ∨ (∃ b, modelMember b xs ∧ modelMember (t299 b r) xs) ∨
 (∃ i b, modelMember b xs ∧ r = t322 i b)
attribute [local irreducible] t299 t322 t323 t324 t325 t326 t327 t328 t329 t330
lemma literalCAxiom_modelCAxiom (n : M) : t332 n ↔ modelCAxiom n := by
 simp only [t332,t15,literalExists_iff,t331,literalOr_iff,literalAnd_iff,t10,t28,t13,t1,literalLe_order,modelCAxiom]
 simp only [or_assoc,and_assoc]
lemma literalCRule_pair (r xs : M) : t335 (modelCantor r xs) ↔ modelCRule r xs := by
 simp only [t335,t20,t15,t16,literalOr_iff,t333,t334,t73,t25,t14,t8,t0,t10,
 literalFst_modelUnpairLeft,literalSnd_modelUnpairRight,modelUnpairLeft_pair,modelUnpairRight_pair,
 literalExists_iff,literalAnd_iff,literalMember_modelMember,literalCAxiom_modelCAxiom,modelCRule]
 simp only [forall_eq,or_assoc]
end ZF207.MM0ModelReplay
