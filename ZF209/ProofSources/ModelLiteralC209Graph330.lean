module
public import ModelLiteralC209Graph329
public import ModelLiteralPairCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def literalC209Constructor330_certificate (e : Nat → M) :
 FunctionGraphCertificate e 3 (fun v=>t330 (v 0) (v 1) (v 2)) := by
 let c299 := literalC209Constructor299_certificate (M:=M) e
 let c300 := literalC209Constructor300_certificate (M:=M) e
 let c302 := literalC209Constructor302_certificate (M:=M) e
 let c322 := literalC209Constructor322_certificate (M:=M) e
 refine ⟨“y a0 a1 a2. ∃w0, ∃w1, ∃w2, ∃w3, ∃w4, ∃w5, ∃w6, ∃w7, ∃w8, ∃w9, ∃w10, ∃w11, ∃w12, ∃w13, ∃w14, ∃w15, ∃w16, ∃w17, ∃w18, ∃w19, ∃w20, ∃w21, ∃w22, ∃w23, ∃w24, ∃w25, ∃w26, ∃w27, ∃w28, ∃w29, ∃w30, ∃w31, ∃w32, ∃w33, ∃w34, ∃w35, !c302.formula w0 a2 a1 ∧ !c302.formula w1 a2 a1 ∧ !c322.formula w2 a0 w1 ∧ !c299.formula w3 w0 w2 ∧ !c300.formula w4 a2 a1 ∧ !c300.formula w5 a2 a1 ∧ !c322.formula w6 a0 w5 ∧ !c299.formula w7 w4 w6 ∧ !c300.formula w8 a2 a0 ∧ !c300.formula w9 a0 a1 ∧ !c300.formula w10 a0 a2 ∧ !c299.formula w11 w9 w10 ∧ !c322.formula w12 a0 w11 ∧ !c300.formula w13 a2 a0 ∧ !c299.formula w14 w13 1 ∧ !c299.formula w15 a0 w14 ∧ !c322.formula w16 a2 w15 ∧ !c299.formula w17 w16 1 ∧ !c299.formula w18 a0 w17 ∧ !c322.formula w19 a2 w18 ∧ !c299.formula w20 w12 w19 ∧ !c322.formula w21 a1 w20 ∧ !c299.formula w22 w21 1 ∧ !c299.formula w23 a0 w22 ∧ !c322.formula w24 a1 w23 ∧ !c299.formula w25 w24 1 ∧ !c299.formula w26 w8 w25 ∧ !c322.formula w27 a2 w26 ∧ !c300.formula w28 a2 a0 ∧ !c299.formula w29 a0 w28 ∧ !c299.formula w30 w29 1 ∧ !c299.formula w31 w27 w30 ∧ !c322.formula w32 a0 w31 ∧ !c299.formula w33 w7 w32 ∧ !c299.formula w34 w3 w33 ∧ !c299.formula w35 w34 1 ∧ y=w35”,?_⟩
 intro v y
 have h299 (z x0 x1:M) : c299.formula.Eval ![z,x0,x1] e ↔ z=t299 x0 x1 := c299.correct ![x0,x1] z
 have h300 (z x0 x1:M) : c300.formula.Eval ![z,x0,x1] e ↔ z=t300 x0 x1 := c300.correct ![x0,x1] z
 have h302 (z x0 x1:M) : c302.formula.Eval ![z,x0,x1] e ↔ z=t302 x0 x1 := c302.correct ![x0,x1] z
 have h322 (z x0 x1:M) : c322.formula.Eval ![z,x0,x1] e ↔ z=t322 x0 x1 := c322.correct ![x0,x1] z
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,literalPairGraph_eval,t330,t44,t45,t33,t32,t31,t30,t29,t28,t303,h299,h300,h302,h322] <;> norm_num
end ZF209.MM0ModelReplay
