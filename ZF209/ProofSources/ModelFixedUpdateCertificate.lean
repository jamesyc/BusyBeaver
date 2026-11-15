module
public import ModelLiteralFunctionUpdateCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma fixedTriple_eval (φ : ArithmeticSemiformula Nat 4) (e : Nat → M) (x : M) :
 (Rew.bind (L:=ℒₒᵣ) ![#0,Semiterm.fvar 0,Semiterm.fvar 1,Semiterm.fvar 2] Semiterm.fvar ▹ φ).Eval ![x] e ↔ φ.Eval ![x,e 0,e 1,e 2] e := by
 rw [Semiformula.eval_rew]
 have hm : (fun i=>Semiterm.val (L:=ℒₒᵣ) ![x] e (![#0,Semiterm.fvar 0,Semiterm.fvar 1,Semiterm.fvar 2] i : ArithmeticSemiterm Nat 1)) = ![x,e 0,e 1,e 2] := by
   funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.cases rfl (fun l=>Fin.cases rfl (fun m=>Fin.elim0 m) l) k) j) i
 change φ.Eval (fun i=>Semiterm.val (L:=ℒₒᵣ) ![x] e (![#0,Semiterm.fvar 0,Semiterm.fvar 1,Semiterm.fvar 2] i : ArithmeticSemiterm Nat 1)) e ↔ _
 rw [hm]
def fixedUpdate_certificate (e : Nat → M) :
 FormulaCertificate e 1 (fun v=>t136 (t120 (e 0)) (e 1) (e 2) (v 0)) where
 formula := Rew.bind (L:=ℒₒᵣ) ![#0,Semiterm.fvar 0,Semiterm.fvar 1,Semiterm.fvar 2] Semiterm.fvar ▹ literalFunctionUpdatePredicate
 correct := by
   intro v
   have hv : ![v 0]=v := by funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
   rw [←hv,fixedTriple_eval]
   exact (literalFunctionUpdatePredicate_eval e (v 0) (e 0) (e 1) (e 2)).symm
end ZF209.MM0ModelReplay
