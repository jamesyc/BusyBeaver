module
public import LiteralProjectionModelAlignment
public import ExactListDecoderGraphs
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalSubOne_modelPredecessor (n : M) : t46 n 1=modelPredecessor n := by
 apply (predecessorGraph_value _ _).mp
 apply (predecessorGraph_eval _ _).mpr
 by_cases hn:n=0
 · subst n; exact Or.inl ⟨rfl,p962 1⟩
 · refine Or.inr ⟨hn,?_⟩
   simpa only [t10,t29,t30,t28,zero_add] using p880 n hn
end ZF207.MM0ModelReplay
