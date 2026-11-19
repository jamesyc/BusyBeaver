module
public import LiteralSourcePredicateDefinitions
public import LiteralSchemaCodeModelAlignment
public import ExactUnaryFormula
public import ExactBinaryFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalAnd_iff (p q : Prop) : t2 p q ↔ p ∧ q := by simp [t2,t1,t0]
lemma literalOr_iff (p q : Prop) : t4 p q ↔ p ∨ q := by simp [t4,t1,t0,or_iff_not_imp_left]
lemma literalExists_iff (p : M → Prop) : t9 p ↔ ∃x,p x := by simp [t9,t1,t8]
/-- Conditional structural bridge: actual row and membership interpretation remain explicit. -/
lemma literalBase_modelBase
 (hrow : ∀r:M, t249 r ↔ modelRowWf r)
 (hmem : ∀a g:M, t144 a g ↔ modelMember a g) (r : M) :
 t270 r ↔ modelBase r := by
 simp only [t270,literalAnd_iff,literalOr_iff,hrow,t257,t258,literalExists_iff,t10,
 literalSequent_modelSequent,hmem,literalImp_modelNode,modelBase]
lemma literalUnary_modelUnary
 (hrow : ∀r:M, t249 r ↔ modelRowWf r)
 (hsub : ∀g h:M, t246 g h ↔ modelContextSub g h)
 (hshift : ∀g:M, t251 g = modelSourceContextShift g)
 (hsubst : ∀d r n:M, t255 d r n = modelSourceSubst d r n)
 (p r : M) : (t271 r p ∨ t280 r p) ↔ modelUnary p r := by
 simp only [t271,t280,literalAnd_iff,literalOr_iff,hrow,t259,t260,t261,t262,t263,t264,t269,t276,t277,t278,
 literalExists_iff,t10,literalSequent_modelSequent,literalCons_modelListCons,literalImp_modelNode,
 literalAnd_modelNode,literalOr_modelNode,literalAll_modelNode,literalEx_modelNode,hsub,hshift,hsubst,t180,t28,
 modelUnary,modelUnaryWith]
 simp only [←and_or_left,or_assoc]
lemma literalBinary_modelBinary
 (hrow : ∀r:M, t249 r ↔ modelRowWf r)
 (hcontext : ∀g:M, t251 g = modelSourceContextShift g)
 (hshift : ∀d n:M, t213 d n = modelSourceShift d n)
 (p q r : M) : (t272 r p q ∨ t281 r p q) ↔ modelBinary p q r := by
 simp only [t272,t281,literalAnd_iff,literalOr_iff,hrow,t265,t266,t267,t268,t279,literalExists_iff,t10,
 literalSequent_modelSequent,literalBranches_modelBranches,literalCons_modelListCons,
 literalImp_modelNode,literalAnd_modelNode,literalOr_modelNode,literalEx_modelNode,hcontext,hshift,t28,modelBinary]
 simp only [←and_or_left,or_assoc]
end ZF207.MM0ModelReplay
