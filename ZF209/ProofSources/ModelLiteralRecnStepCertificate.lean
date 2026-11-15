module
public import ModelLiteralPairCompositionCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def literalRecnStep_certificate {e : Nat → M} {A : M → Prop}
 (p : FormulaCertificate e 1 (fun v => A (v 0))) :
 FormulaCertificate e 1 (fun v => t82 (fun x => t63 (t29 (t64 x)) (t84 A x)) (v 0)) := by
 let succGraph : FunctionGraphCertificate e 1 (fun v => v 0+1) := {
   formula := “y x. y=x+1”
   correct := by intro v y; rfl
 }
 let fstSucc := succGraph.compose (F := fun x : M => x+1) (G := fun x => t64 x) (literalFst_certificate e)
 exact literalGraph_certificate (F := fun x => t63 (t29 (t64 x)) (t84 A x))
  (literalPairFunctions_certificate (F := fun x => t29 (t64 x)) (G := fun x => t84 A x) fstSucc (literalApply_certificate p))
end ZF209.MM0ModelReplay
