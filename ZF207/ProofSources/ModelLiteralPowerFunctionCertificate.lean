module
public import ModelLiteralExponentCertificate
public import ModelUnaryFunctionCertificates
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def literalPowerFunction_certificate (e : Nat → M) (j : Nat) :
 FunctionGraphCertificate e 1 (fun v => t117 (e j) (v 0)) where
 formula := Rew.bind (L:=ℒₒᵣ) ![#0,#1,Semiterm.fvar j] Semiterm.fvar ▹ (literalExponent_certificate e).formula
 correct := by
   intro v y
   rw [Semiformula.eval_rew]
   have hm : (fun i => Semiterm.val (L:=ℒₒᵣ) (y :> v) e (![#0,#1,Semiterm.fvar j] i : ArithmeticSemiterm Nat 2)) = ![y,v 0,e j] := by
     funext i; exact Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun m => Fin.elim0 m) l) k) i
   change (literalExponent_certificate e).formula.Eval (fun i => Semiterm.val (L:=ℒₒᵣ) (y :> v) e (![#0,#1,Semiterm.fvar j] i : ArithmeticSemiterm Nat 2)) e ↔ _
   rw [hm]
   exact (literalExponent_certificate e).correct ![v 0,e j] y
end ZF207.MM0ModelReplay
