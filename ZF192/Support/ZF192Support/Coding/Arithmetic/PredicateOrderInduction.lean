module
public import ZF192Support.Coding.Arithmetic.FormulaCertificates
public import ZF192Support.Coding.Histories.TraceEquations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.MM0ModelPeano.FormulaCertificate
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {e : Nat → M} {P : (Fin 1 → M) → Prop}

def orderBoundedAll (a : FormulaCertificate e 1 P) :
 FormulaCertificate e 1 (fun v => ∀y<v 0,P ![y]) where
 formula := ∀¹ ((“#0 < #1” : ArithmeticSemiformula Nat 2) 🡒
   (Rew.bind (L:=ℒₒᵣ) ![#0] Semiterm.fvar ▹ a.formula))
 correct := by
  intro v
  simp [Semiformula.eval_rew,Function.comp_def]
  simp only [Matrix.constant_eq_singleton,←a.correct]
theorem orderInduction (a : FormulaCertificate e 1 P)
 (step : ∀x,(∀y<x,P ![y]) → P ![x]) : ∀x,P ![x] := by
 have h := a.orderBoundedAll.induction
 have h0 : ∀y<(0:M),P ![y] := by intro y hy; exact False.elim (not_lt_zero hy)
 have hs : ∀x : M,(∀y<x,P ![y]) → ∀y<x+1,P ![y] := by
  intro x hx y hy
  rcases lt_or_eq_of_le (lt_succ_iff_le.mp hy) with h|h
  · exact hx y h
  · subst y; exact step x hx
 intro x
 exact h h0 hs (x+1) x (lt_add_one x)
end ZF192Support.MM0ModelPeano.FormulaCertificate
