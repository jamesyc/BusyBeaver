module
public import ModelReplay1449
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalSubstitute_value (F : M → M) (x : M) : t43 x F=F x := by
 apply ZF209.MM0ModelPeano.theid
 apply (ZF209.MM0ModelPeano.eqs_iff _ _).mpr
 intro y
 exact ZF209.MM0ModelPeano.sb_iff x (fun z => y=F z)

def literalSubstitute_certificate {e : Nat → M} {F : M → M}
 (g : FunctionGraphCertificate e 1 (fun v => F (v 0))) :
 FunctionGraphCertificate e 1 (fun v => t43 (v 0) F) where
 formula := g.formula
 correct := by
   intro v y
   rw [literalSubstitute_value]
   exact g.correct v y
end ZF209.MM0ModelReplay
