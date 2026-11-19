module
public import ExactSchemaRenameGraphs
public import ExactBinaryFormula
public import ExactAllPrefixEquations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def modelNumericSeparation (b : M) : M := (modelSourceNode 6 (modelSourceNode 7 (modelSourceNode 6 (modelSourceNode 3 (modelSourceNode 5 (modelSourceNode 1 0 1) (modelSourceNode 3 (modelSourceNode 1 0 2) b)) (modelSourceNode 5 (modelSourceNode 3 (modelSourceNode 1 0 2) b) (modelSourceNode 1 0 1))) 0) 0) 0)
def numericSeparationGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “z b. ∃ x0, ∃ x1, ∃ x2, ∃ x3, ∃ x4, ∃ x5, ∃ x6, ∃ x7, ∃ x8, ∃ x9, ∃ x10, !sourceNodeGraph x0 1 0 1 ∧ !sourceNodeGraph x1 1 0 2 ∧ !sourceNodeGraph x2 3 x1 b ∧ !sourceNodeGraph x3 5 x0 x2 ∧ !sourceNodeGraph x4 1 0 2 ∧ !sourceNodeGraph x5 3 x4 b ∧ !sourceNodeGraph x6 1 0 1 ∧ !sourceNodeGraph x7 5 x5 x6 ∧ !sourceNodeGraph x8 3 x3 x7 ∧ !sourceNodeGraph x9 6 x8 0 ∧ !sourceNodeGraph x10 7 x9 0 ∧ !sourceNodeGraph z 6 x10 0”
lemma numericSeparationGraph_eval (z b : M) : numericSeparationGraph.val.Evalb ![z,b] ↔ z=modelNumericSeparation b := by
 simp [numericSeparationGraph,modelNumericSeparation,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,ruleNode_defined.iff,numeral_eq_natCast]
lemma modelNumericSeparation_nat (b : Nat) : modelNumericSeparation b=numericSeparation b := by
 simp only [modelNumericSeparation,modelSourceNode_nat,numericSeparation,numericIff,numericFunctionality]
 rfl
noncomputable def modelNumericReplacement (a b c : M) : M := (modelSourceNode 5 (modelSourceNode 6 (modelSourceNode 6 (modelSourceNode 6 (modelSourceNode 5 a (modelSourceNode 5 b (modelSourceNode 2 1 0))) 0) 0) 0) (modelSourceNode 6 (modelSourceNode 7 (modelSourceNode 6 (modelSourceNode 3 (modelSourceNode 5 (modelSourceNode 1 0 1) (modelSourceNode 7 (modelSourceNode 3 (modelSourceNode 1 0 3) c) 0)) (modelSourceNode 5 (modelSourceNode 7 (modelSourceNode 3 (modelSourceNode 1 0 3) c) 0) (modelSourceNode 1 0 1))) 0) 0) 0))
def numericReplacementGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
 “z a b c. ∃ x0, ∃ x1, ∃ x2, ∃ x3, ∃ x4, ∃ x5, ∃ x6, ∃ x7, ∃ x8, ∃ x9, ∃ x10, ∃ x11, ∃ x12, ∃ x13, ∃ x14, ∃ x15, ∃ x16, ∃ x17, ∃ x18, ∃ x19, !sourceNodeGraph x0 2 1 0 ∧ !sourceNodeGraph x1 5 b x0 ∧ !sourceNodeGraph x2 5 a x1 ∧ !sourceNodeGraph x3 6 x2 0 ∧ !sourceNodeGraph x4 6 x3 0 ∧ !sourceNodeGraph x5 6 x4 0 ∧ !sourceNodeGraph x6 1 0 1 ∧ !sourceNodeGraph x7 1 0 3 ∧ !sourceNodeGraph x8 3 x7 c ∧ !sourceNodeGraph x9 7 x8 0 ∧ !sourceNodeGraph x10 5 x6 x9 ∧ !sourceNodeGraph x11 1 0 3 ∧ !sourceNodeGraph x12 3 x11 c ∧ !sourceNodeGraph x13 7 x12 0 ∧ !sourceNodeGraph x14 1 0 1 ∧ !sourceNodeGraph x15 5 x13 x14 ∧ !sourceNodeGraph x16 3 x10 x15 ∧ !sourceNodeGraph x17 6 x16 0 ∧ !sourceNodeGraph x18 7 x17 0 ∧ !sourceNodeGraph x19 6 x18 0 ∧ !sourceNodeGraph z 5 x5 x19”
lemma numericReplacementGraph_eval (z a b c : M) : numericReplacementGraph.val.Evalb ![z,a,b,c] ↔ z=modelNumericReplacement a b c := by
 simp [numericReplacementGraph,modelNumericReplacement,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,ruleNode_defined.iff,numeral_eq_natCast]
lemma modelNumericReplacement_nat (a b c : Nat) : modelNumericReplacement a b c=numericReplacement a b c := by
 simp only [modelNumericReplacement,modelSourceNode_nat,numericReplacement,numericIff,numericFunctionality]
 rfl
end ZFR.ArithmeticRepresentation
