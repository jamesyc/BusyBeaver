module
public import ModelLiteralC209Graph300
public import ModelLiteralPairCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def literalC209Constructor302_certificate (e : Nat → M) :
 FunctionGraphCertificate e 2 (fun v=>t302 (v 0) (v 1)) := by
 refine ⟨“y a0 a1. ∃w0, !literalPairGraph w0 a0 a1 ∧ y=((4*w0)+3)”,?_⟩
 intro v y
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,literalPairGraph_eval,t302,t44,t45,t33,t32,t31,t30,t29,t28,t303] <;> norm_num
end ZF209.MM0ModelReplay
