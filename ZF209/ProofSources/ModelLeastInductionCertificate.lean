module
public import ModelReplay1541
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def selectUnary {k} (j : Fin k) (φ : ArithmeticSemiformula Nat 1) : ArithmeticSemiformula Nat k :=
 Rew.bind (L := ℒₒᵣ) ![Semiterm.bvar j] Semiterm.fvar ▹ φ

lemma selectUnary_eval {k} (j : Fin k) (φ : ArithmeticSemiformula Nat 1)
 (v : Fin k → M) (e : Nat → M) :
 (selectUnary j φ).Eval v e ↔ φ.Eval ![v j] e := by
 rw [selectUnary,Semiformula.eval_rew]
 have hb : Semiterm.val v e ∘ (Rew.bind (L := ℒₒᵣ) ![Semiterm.bvar j] Semiterm.fvar) ∘ Semiterm.bvar = ![v j] := by
   funext i; exact Fin.cases rfl (fun i => Fin.elim0 i) i
 have hf : Semiterm.val v e ∘ (Rew.bind (L := ℒₒᵣ) ![Semiterm.bvar j] Semiterm.fvar) ∘ Semiterm.fvar = e := by funext i; rfl
 rw [hb,hf]

def leastInductionFormula (φ : ArithmeticSemiformula Nat 1) : ArithmeticSemiformula Nat 1 :=
 (∼(∀¹ (selectUnary 0 φ 🡒 “∃q,(#2+1)+#0=#1”))) 🡒
 ∃¹ (selectUnary 0 φ ⋏ (∀¹ (selectUnary 0 φ 🡒 “∃q,#2+#0=#1”)))

def FormulaCertificate.leastInduction {e : Nat → M} {P : M → Prop}
 (p : FormulaCertificate e 1 (fun v => P (v 0))) :
 FormulaCertificate e 1 (fun v =>
   (¬∀y,P y → ∃q,(v 0+1)+q=y) → ∃z,P z ∧ ∀y,P y → ∃q,z+q=y) where
 formula := leastInductionFormula p.formula
 correct := by
   intro v
   simp only [leastInductionFormula]
   simp [selectUnary_eval,←p.correct]
end ZF209.MM0ModelPeano
