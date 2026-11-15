module
public import LiteralSchemaCodeDefinitions
public import LiteralSourceCodeModelAlignment
public import ExactFixedAxiomFormula
public import ExactSchemaConstructorGraphs
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZFR ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalFixed196_model : (t196 (M:=M))=modelFixedFormula fixedRefl := by
 simp [t196,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelFixedFormula,fixedRefl,t180,t32,t31,t30,t29,t28] <;> norm_num
lemma literalFixed197_model : (t197 (M:=M))=modelFixedFormula fixedSym := by
 simp [t197,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelFixedFormula,fixedSym,t180,t32,t31,t30,t29,t28] <;> norm_num
lemma literalFixed198_model : (t198 (M:=M))=modelFixedFormula fixedTrans := by
 simp [t198,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelFixedFormula,fixedTrans,t180,t32,t31,t30,t29,t28] <;> norm_num
lemma literalFixed199_model : (t199 (M:=M))=modelFixedFormula fixedEqElem := by
 simp [t199,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelFixedFormula,fixedEqElem,t180,t32,t31,t30,t29,t28] <;> norm_num
lemma literalFixed200_model : (t200 (M:=M))=modelFixedFormula fixedExt := by
 simp [t200,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelFixedFormula,fixedExt,t180,t32,t31,t30,t29,t28] <;> norm_num
lemma literalFixed201_model : (t201 (M:=M))=modelFixedFormula fixedEmpty := by
 simp [t201,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelFixedFormula,fixedEmpty,t180,t32,t31,t30,t29,t28] <;> norm_num
lemma literalFixed202_model : (t202 (M:=M))=modelFixedFormula fixedPair := by
 simp [t202,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelFixedFormula,fixedPair,t180,t32,t31,t30,t29,t28] <;> norm_num
lemma literalFixed203_model : (t203 (M:=M))=modelFixedFormula fixedUnion := by
 simp [t203,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelFixedFormula,fixedUnion,t180,t32,t31,t30,t29,t28] <;> norm_num
lemma literalFixed204_model : (t204 (M:=M))=modelFixedFormula fixedPower := by
 simp [t204,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelFixedFormula,fixedPower,t180,t32,t31,t30,t29,t28] <;> norm_num
lemma literalFixed205_model : (t205 (M:=M))=modelFixedFormula fixedOmega := by
 simp [t205,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelFixedFormula,fixedOmega,t180,t32,t31,t30,t29,t28] <;> norm_num
lemma literalFixed206_model : (t206 (M:=M))=modelFixedFormula fixedFoundation := by
 simp [t206,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelFixedFormula,fixedFoundation,t180,t32,t31,t30,t29,t28] <;> norm_num
lemma literalCons_modelListCons (a b : M) : t131 a b=modelListCons a b := by
 simp [t131,t29,literalPair_modelCantor,modelListCons]
lemma literalIff_model (a b : M) : t219 a b=modelSourceNode 3 (modelSourceNode 5 a b) (modelSourceNode 5 b a) := by
 simp only [t219,literalAnd_modelNode,literalImp_modelNode]
lemma literalSeparation_model (a : M) : t220 a=modelNumericSeparation a := by
 simp [t220,literalIff_model,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelNumericSeparation,t31,t30,t29,t28] <;> norm_num
lemma literalReplacement_model (a b c : M) : t222 a b c=modelNumericReplacement a b c := by
 simp [t222,t221,literalIff_model,literalMem_modelNode,literalEq_modelNode,literalAnd_modelNode,literalOr_modelNode,literalImp_modelNode,literalAll_modelNode,literalEx_modelNode,modelNumericReplacement,t32,t31,t30,t29,t28] <;> norm_num
lemma literalFixedAxiom_iff (z : M) : (t295 z ∨ z=t206) ↔ modelFixedAxiom z := by
 classical
 simp [t295,t4,t1,t0,t10,imp_iff_not_or,or_assoc,literalFixed196_model,literalFixed197_model,literalFixed198_model,literalFixed199_model,literalFixed200_model,literalFixed201_model,literalFixed202_model,literalFixed203_model,literalFixed204_model,literalFixed205_model,literalFixed206_model,modelFixedAxiom,fixedAxiomList]
end ZF209.MM0ModelReplay
