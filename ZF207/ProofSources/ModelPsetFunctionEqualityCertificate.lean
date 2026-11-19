module
public import ModelGraphEqualityCertificate
public import ModelLiteralPsetMembershipCertificate
public import ModelLiteralApplicationCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def literalPsetAt_certificate (e : Nat → M) (j : Nat) :
 FormulaCertificate e 1 (fun v => t109 (e j) (v 0)) := by
 simpa only [Nat.zero_add] using
  (literalPsetMembership_certificate (fun i => e (i+j))).reindexParameters e (fun i => i+j) (fun _ => rfl)

noncomputable def literalPsetFunctionEquality_certificate (e : Nat → M) (i j : Nat) :
 FormulaCertificate e 1 (fun v => t84 (t109 (e i)) (v 0)=t84 (t109 (e j)) (v 0)) :=
 (literalApply_certificate (literalPsetAt_certificate e i)).equal
  (literalApply_certificate (literalPsetAt_certificate e j))
end ZF207.MM0ModelReplay
