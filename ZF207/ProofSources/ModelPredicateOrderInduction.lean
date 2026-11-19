module
public import ModelFormulaCertificates
public import ExactTraceModelEquations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelPeano.FormulaCertificate
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {e : Nat → M} {P Q : (Fin 1 → M) → Prop}
def iffCert (a : FormulaCertificate e 1 P) (b : FormulaCertificate e 1 Q) :
 FormulaCertificate e 1 (fun v => P v ↔ Q v) where
 formula := (a.formula 🡒 b.formula) ⋏ (b.formula 🡒 a.formula)
 correct := by intro v; simp [←a.correct,←b.correct,iff_iff_implies_and_implies]
def orderBoundedAll (a : FormulaCertificate e 1 P) :
 FormulaCertificate e 1 (fun v => ∀y<v 0,P ![y]) where
 formula := ∀¹ ((“#0 < #1” : ArithmeticSemiformula Nat 2) 🡒
   (Rew.bind (L:=ℒₒᵣ) ![#0] Semiterm.fvar ▹ a.formula))
 correct := by
  intro v
  simp [Semiformula.eval_rew,Function.comp_def]
  have hv (y:M) : (fun _ : Fin 1=>y)=![y] := by
   funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
  simp only [hv,←a.correct]
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
def fromSemisentence (e : Nat → M) (φ : ArithmeticSemisentence 1) :
 FormulaCertificate e 1 (fun v => φ.Evalb v) where
 formula := Rew.rewriteMap (L:=ℒₒᵣ) (Empty.elim : Empty → Nat) ▹ φ
 correct := by intro v; simp [Semiformula.eval_rewriteMap,Function.comp_def,Empty.eq_elim]
end ZF207.MM0ModelPeano.FormulaCertificate
