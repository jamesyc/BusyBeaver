module
public import ModelLiteralSetCodeCertificate
public import ModelGraphEqualityCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma fixedSecond_eval (φ : ArithmeticSemiformula Nat 2) (e : Nat → M) (x : M) :
 (Rew.bind (L:=ℒₒᵣ) ![#0,Semiterm.fvar 0] Semiterm.fvar ▹ φ).Eval ![x] e ↔ φ.Eval ![x,e 0] e := by
 rw [Semiformula.eval_rew]
 have hm : (fun i => Semiterm.val (L:=ℒₒᵣ) ![x] e (![#0,Semiterm.fvar 0] i : ArithmeticSemiterm Nat 1)) = ![x,e 0] := by
   funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.elim0 k) j) i
 change φ.Eval (fun i => Semiterm.val (L:=ℒₒᵣ) ![x] e (![#0,Semiterm.fvar 0] i : ArithmeticSemiterm Nat 1)) e ↔ _
 rw [hm]
def literalBitParameter_certificate (e : Nat → M) :
 FormulaCertificate e 1 (fun v => t120 (e 0) (v 0)) where
 formula := Rew.bind (L:=ℒₒᵣ) ![#0,Semiterm.fvar 0] Semiterm.fvar ▹ literalBitMembershipFormula
 correct := by
   intro v
   have hv : ![v 0]=v := by funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
   rw [←hv,fixedSecond_eval]
   exact (literalBitMembershipFormula_eval e (v 0) (e 0)).symm
noncomputable def literalBitAt_certificate (e : Nat → M) (j : Nat) :
 FormulaCertificate e 1 (fun v => t120 (e j) (v 0)) := by
 simpa only [Nat.zero_add] using
  (literalBitParameter_certificate (fun i=>e (i+j))).reindexParameters e (fun i=>i+j) (fun _=>rfl)
end ZF207.MM0ModelReplay
