module
public import ModelLiteralGrecStepCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def FunctionGraphCertificate.bindFirst {e : Nat → M} {F : M → M → M}
 (g : ∀a : M, FunctionGraphCertificate (fun i=>Nat.casesOn i a e) 1 (fun v=>F a (v 0)))
 (h : ∀a,(g 0).formula=(g a).formula) :
 FunctionGraphCertificate e 2 (fun v=>F (v 1) (v 0)) := by
 refine ⟨Rew.bind (L:=ℒₒᵣ) ![#0,#1] (fun i=>Nat.casesOn i #2 Semiterm.fvar) ▹ (g 0).formula,?_⟩
 intro v y
 rw [Semiformula.eval_rew]
 have hb : (Semiterm.val (L:=ℒₒᵣ) (y :> v) e ∘ (Rew.bind (L:=ℒₒᵣ) ![#0,#1] (fun i : Nat=>Nat.casesOn i #2 Semiterm.fvar)) ∘ Semiterm.bvar) = ![y,v 0] := by
  funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.elim0 k) j) i
 have hf : (Semiterm.val (L:=ℒₒᵣ) (y :> v) e ∘ (Rew.bind (L:=ℒₒᵣ) ![#0,#1] (fun i : Nat=>Nat.casesOn i #2 Semiterm.fvar)) ∘ Semiterm.fvar) = (fun i=>Nat.casesOn i (v 1) e) := by
  funext i; cases i <;> rfl
 rw [hb,hf,h (v 1)]
 exact (g (v 1)).correct ![v 0] y
end ZF207.MM0ModelPeano
