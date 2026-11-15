module
public import LiteralPairModelAlignment
public import ModelApplicationCertificates
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalApply_modelApply (A : M → Prop) (x : M) :
 t84 A x = modelApply A x := by
 unfold t84 t16 t15 t40 modelApply
 simp only [literalPair_modelCantor]

def literalApply_certificate {e : Nat → M} {A : M → Prop}
 (p : FormulaCertificate e 1 (fun v => A (v 0))) :
 FunctionGraphCertificate e 1 (fun v => t84 A (v 0)) where
 formula := p.application.formula
 correct := by
   intro v y
   rw [literalApply_modelApply]
   exact p.application.correct v y
end ZF209.MM0ModelReplay
