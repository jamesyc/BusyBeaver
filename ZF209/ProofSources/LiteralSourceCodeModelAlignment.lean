module
public import LiteralSourceCodeDefinitions
public import LiteralProjectionModelAlignment
public import ExactRowCodingGraphs
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalNode_modelSourceNode (t a b : M) : t181 t a b=modelSourceNode t a b := by
 simp [t181,literalPair_modelCantor,t37,t36,t35,t34,t33,t32,t31,t30,t29,t28,t44,t45,modelSourceNode] <;> norm_num
lemma literalSequent_modelSequent (g a : M) : t247 g a=modelSequent g a := by
 simp only [t247,literalPair_modelCantor,t28,modelSequent]
lemma literalBranches_modelBranches (g a b c : M) : t248 g a b c=modelBranches g a b c := by
 simp [t248,literalPair_modelCantor,t30,t29,t28,modelBranches] <;> norm_num
lemma literalMem_modelNode (a b : M) : t182 a b=modelSourceNode 1 a b := by
 simp [t182,literalNode_modelSourceNode,t30,t29,t28] <;> norm_num
lemma literalEq_modelNode (a b : M) : t183 a b=modelSourceNode 2 a b := by
 simp [t183,literalNode_modelSourceNode,t31,t30,t29,t28] <;> norm_num
lemma literalAnd_modelNode (a b : M) : t184 a b=modelSourceNode 3 a b := by
 simp [t184,literalNode_modelSourceNode,t32,t31,t30,t29,t28] <;> norm_num
lemma literalOr_modelNode (a b : M) : t185 a b=modelSourceNode 4 a b := by
 simp [t185,literalNode_modelSourceNode,t33,t32,t31,t30,t29,t28] <;> norm_num
lemma literalImp_modelNode (a b : M) : t186 a b=modelSourceNode 5 a b := by
 simp [t186,literalNode_modelSourceNode,t34,t33,t32,t31,t30,t29,t28] <;> norm_num
lemma literalAll_modelNode (a : M) : t187 a=modelSourceNode 6 a 0 := by
 simp [t187,literalNode_modelSourceNode,t35,t34,t33,t32,t31,t30,t29,t28] <;> norm_num
lemma literalEx_modelNode (a : M) : t188 a=modelSourceNode 7 a 0 := by
 simp [t188,literalNode_modelSourceNode,t36,t35,t34,t33,t32,t31,t30,t29,t28] <;> norm_num
end ZF209.MM0ModelReplay
