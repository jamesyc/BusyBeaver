module
public import LiteralMemberModelAlignment
public import ModelReplay2756
public import LiteralSourceCodeModelAlignment
public import LiteralRadix8ModelAlignment
public import ExactSourceDecoderEquations
public import LiteralFiniteRuleModelAlignment
public import ModelLiteralBitMembershipCertificate
public import ModelLiteralDomainSizeCertificate
public import ModelLiteralSetCodeCertificate
public import LiteralSourcePredicateDefinitions
public import ExactTheoryProofFormula
public import ExactContextSubDefinability
public import ExactContextWfSentences
public import ModelLiteralConditionalCertificate
public import LiteralPredecessorModelAlignment
public import ExactSchemaIndexGraphs
public import ExactIndexEquations
public import ExactTransformBranchGraph
public import ModelLiteralCourseRecCertificate
public import ModelReplay1892
public import LiteralSchemaCodeModelAlignment
public import ExactSourceShiftSentences
public import ModelPredicateOrderInduction
public import ExactSourceBoundEquations
public import ExactFixedAxiomClosed
public import ModelLiteralContextCodeCertificate
public import ModelLiteralTraceCertificate
public import ModelLiteralGrecStepCertificate
public import ExactSubstBranchGraph
public import ExactSourceSubstSentences
public import ExactContextShiftSentences
public import ModelLiteralC207Graph330
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZF207.MM0ModelReplay ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
structure Store (M : Type*) where
 t : M
 w : M
 d : M
 h : M
inductive Command (M : Type*) where
 | shift
 | mp (x:M)
 | ax (a x y:M)
noncomputable def gate (a d h:M) : M := if a≠d ∧ a≠h then t330 a d h else 0
noncomputable def heads (a d h oldd oldh:M) : List M :=
 [t323 a d h,t324 a d h,t325 a d h,t326 a d h,t327 a d h,t328 a d h,t329 a d h oldd,t322 oldd oldh]
noncomputable def modelCommandEval : Command M → Store M → Option (Store M)
 | .shift,s => if s.t+s.h=1 then none else some ⟨s.h,modelUnpairRight s.w,s.d,modelUnpairLeft s.w⟩
 | .mp x,s => let v:=s.d+x
   if t299 s.t v=s.h then some ⟨v,modelCantor 0 s.w,v,0⟩ else some ⟨0,s.w,v,0⟩
 | .ax a x y,s => some ⟨gate a (s.d+x) (s.h+y),
   (heads a (s.d+x) (s.h+y) s.d s.h ++ [s.t]).foldr modelCantor s.w,0,0⟩
/-- Only external FINITE macro lists. Not an internal nonstandard-length evaluator. -/
noncomputable def modelCommandsEval : List (Command M) → Store M → Option (Store M)
 | [],s => some s
 | c::cs,s => (modelCommandEval c s).bind (modelCommandsEval cs)
lemma modelImp_value (a b:M) : t299 a b=4*modelCantor a b := by
 simp [t299,t45,t33,t32,t31,t30,t29,t28,literalPair_modelCantor]; norm_num
lemma modelAll_value (i a:M) : t322 i a=4*modelCantor a i+2 := by
 simp [t322,t44,t45,t33,t32,t31,t30,t29,t28,literalPair_modelCantor]; norm_num
lemma four_mul_ne_one (x:M) : 4*x≠1 := by
 intro h
 by_cases hx:x=0
 · simp [hx] at h
 · have hx1 : 1≤x := by simpa using (succ_le_iff_lt.mpr (pos_iff_ne_zero.mpr hx))
   have hh : (4:M)≤4*x := by simpa using mul_le_mul_of_nonneg_left hx1 (by simp : (0:M)≤4)
   rw [h] at hh
   norm_num at hh
lemma four_mul_ne_four_add_two (x y:M) : 4*x≠4*y+2 := by
 intro h
 rcases lt_trichotomy x y with hxy|he|hyx
 · have hle : 4*x≤4*y := mul_le_mul_of_nonneg_left (le_of_lt hxy) (by simp)
   rw [h] at hle
   have hh : 4*y<4*y+2 := by simp
   exact (not_le_of_gt hh) hle
 · rw [he] at h
   have hh : 4*y<4*y+2 := by simp
   exact (ne_of_lt hh) h
 · have hh : 4*(y+1)≤4*x := mul_le_mul_of_nonneg_left (succ_le_iff_lt.mpr hyx) (by simp)
   rw [h,mul_add,mul_one] at hh
   have hn : 4*y+2<4*y+4 := by simpa using (show (2:M)<4 from (model_natCast_lt (M:=M) (show (2:Nat)<4 by decide)))
   exact (not_le_of_gt hn) hh
end ZF207.ModelCommands
