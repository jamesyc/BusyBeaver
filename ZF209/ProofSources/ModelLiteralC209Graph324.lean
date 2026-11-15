module
public import ModelLiteralC209Graph323
public import ModelLiteralPairCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def literalC209Constructor324_certificate (e : Nat → M) :
 FunctionGraphCertificate e 3 (fun v=>t324 (v 0) (v 1) (v 2)) := by
 let c299 := literalC209Constructor299_certificate (M:=M) e
 let c302 := literalC209Constructor302_certificate (M:=M) e
 let c322 := literalC209Constructor322_certificate (M:=M) e
 refine ⟨“y a0 a1 a2. ∃w0, ∃w1, ∃w2, ∃w3, !c302.formula w0 a2 a1 ∧ !c299.formula w1 w0 1 ∧ !c322.formula w2 a1 w1 ∧ !c299.formula w3 w2 1 ∧ y=w3”,?_⟩
 intro v y
 have h299 (z x0 x1:M) : c299.formula.Eval ![z,x0,x1] e ↔ z=t299 x0 x1 := c299.correct ![x0,x1] z
 have h302 (z x0 x1:M) : c302.formula.Eval ![z,x0,x1] e ↔ z=t302 x0 x1 := c302.correct ![x0,x1] z
 have h322 (z x0 x1:M) : c322.formula.Eval ![z,x0,x1] e ↔ z=t322 x0 x1 := c322.correct ![x0,x1] z
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,literalPairGraph_eval,t324,t44,t45,t33,t32,t31,t30,t29,t28,t303,h299,h302,h322] <;> norm_num
end ZF209.MM0ModelReplay
