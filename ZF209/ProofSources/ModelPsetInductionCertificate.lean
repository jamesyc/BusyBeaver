module
public import ModelLeastInductionCertificate
public import ModelMM0BetaMembership
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Context order k,c,n; free parameter0 is the common multiple b. -/
def psetBetaAt : ArithmeticSemiformula Nat 3 :=
 Rew.bind (L := ℒₒᵣ) ![#0,&0,#1] Semiterm.fvar ▹ mm0BetaMembershipFormula
lemma psetBetaAt_eval (e : Nat → M) (v : Fin 3 → M) :
 psetBetaAt.Eval v e ↔ mm0BetaMembership (e 0) (v 1) (v 0) := by
 rw [psetBetaAt,Semiformula.eval_rew]
 have hb : Semiterm.val v e ∘ (Rew.bind (L := ℒₒᵣ) ![#0,&0,#1] Semiterm.fvar) ∘ Semiterm.bvar = ![v 0,e 0,v 1] := by
  funext i
  exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.cases rfl (fun l=>Fin.elim0 l) k) j) i
 have hf : Semiterm.val v e ∘ (Rew.bind (L := ℒₒᵣ) ![#0,&0,#1] Semiterm.fvar) ∘ Semiterm.fvar = e := by
  funext i; rfl
 rw [hb,hf]
 exact mm0BetaMembership_eval e (v 0) (e 0) (v 1)
/-- Actual syntax only: existence of the finite coding witness is not assumed. -/
def psetInductionFormula (φ : ArithmeticSemiformula Nat 1) : ArithmeticSemiformula Nat 1 :=
 ∃¹ (“0<#0” ⋏ (∀¹ (psetBetaAt 🡘 (“#0<#2” ⋏ selectUnary 0 φ))))
def FormulaCertificate.psetInduction {e : Nat → M} {P : M → Prop}
 (p : FormulaCertificate e 1 (fun v => P (v 0))) :
 FormulaCertificate e 1 (fun v => ∃c,0<c ∧ ∀k,
   mm0BetaMembership (e 0) c k ↔ k<v 0 ∧ P k) where
 formula := psetInductionFormula p.formula
 correct := by
  intro v
  simp [psetInductionFormula,psetBetaAt_eval,selectUnary_eval,←p.correct]
/-- Free parameters0=b and1=ambient bound; this is just the actual antecedent syntax. -/
def psetAntecedentFormula : ArithmeticSemiformula Nat 1 :=
 “n. 0<&0 ∧ ∀j,(0<j ∧ j≤&1) → ∃q,q*j=&0”
def psetAntecedent_certificate (e : Nat → M) :
 FormulaCertificate e 1 (fun _ => 0<e 0 ∧ ∀j,(0<j ∧ j≤e 1) → ∃q,q*j=e 0) where
 formula := psetAntecedentFormula
 correct := by intro v; simp [psetAntecedentFormula]
end ZF209.MM0ModelPeano
