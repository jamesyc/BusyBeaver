module
public import ModelUnaryFunctionCertificates
public import ModelReplay1904
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalConditional_value (P : Prop) (a b : M) :
 t50 P a b = @ite M P (Classical.propDecidable _) a b := by
 apply ZF209.MM0ModelPeano.theid
 apply (ZF209.MM0ModelPeano.eqs_iff _ _).mpr
 intro y
 classical
 by_cases h : P <;> simp [t5,t4,t15,t2,t0,t1,t10,h]

def literalConditional_certificate {e : Nat → M} {P : M → Prop} {F G : M → M}
 (p : FormulaCertificate e 1 (fun v => P (v 0)))
 (f : FunctionGraphCertificate e 1 (fun v => F (v 0)))
 (g : FunctionGraphCertificate e 1 (fun v => G (v 0))) :
 FunctionGraphCertificate e 1 (fun v => t50 (P (v 0)) (F (v 0)) (G (v 0))) where
 formula := (FunctionGraphCertificate.ifThenElse p f g).formula
 correct := by
   intro v y
   rw [literalConditional_value]
   exact (FunctionGraphCertificate.ifThenElse p f g).correct v y
end ZF209.MM0ModelReplay
