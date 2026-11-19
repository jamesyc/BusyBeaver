module
public import ExactMemberBound
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def theoryContextFormula (ax : 𝚺ᴬ₁.Semisentence 1) : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
 “g. ∀ a<g, ∃ u, !memberCodeGraph u a g ∧ (u=0 ∨ !ax a)”
def modelTheoryContext (A : M → Prop) (g : M) := ∀ a<g, modelMemberCode a g=0 ∨ A a
lemma theoryContextFormula_defined (ax : 𝚺ᴬ₁.Semisentence 1) (A : M → Prop)
 (hA : 𝚺ᴬ₁.DefinedPred A ax) :
 𝚺ᴬ₁.DefinedPred (modelTheoryContext A) (theoryContextFormula ax) := .mk (by
 intro v
 simp [theoryContextFormula,modelTheoryContext,Semiformula.eval_rew,Function.comp_def,
 Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,memberCodeGraph_defined.iff,hA.iff])
lemma modelTheoryContext_nat (A : Nat → Prop) (g : Nat) :
 modelTheoryContext A g ↔ ∀a,sourceMember a g → A a := by
 constructor
 · intro h a ha
   have hm := (modelMember_nat a g).mpr ha
   have hx := h a (modelMember_lt_nat a g hm)
   rcases hx with hz|ha
   · unfold modelMember at hm; omega
   · exact ha
 · intro h a _
   rcases modelMemberCode_boolean a g with hz|hz
   · exact Or.inl hz
   · exact Or.inr (h a ((modelMember_nat a g).mp hz))
end ZFR.ArithmeticRepresentation
