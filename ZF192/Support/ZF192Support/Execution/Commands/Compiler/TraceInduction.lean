module
public import ZF192Support.Calculus.Internal.TraceRules
public import ZF192Support.Coding.Arithmetic.PredicateOrderInduction
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZF192Support.MM0ModelPeano ZFR.ArithmeticRepresentation ZF192Support.Halting
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Induction over an internal C proof trace. The compiler invariant must itself
have an actual first-order formula certificate; arbitrary external predicates
are deliberately not admitted. -/
theorem modelCTrace_induction (e : Nat → M) (P : M → Prop)
 (cert : FormulaCertificate e 1 (fun v=>P (v 0)))
 (zero : P 0)
 (step : ∀a b,modelTrace cRule b → P b → cRule a b → P (modelListCons a b)) :
 ∀n,modelTrace cRule n → P n := by
 let trace : FormulaCertificate e 1 (fun v => modelTrace cRule (v 0)) :=
   ⟨Rewriting.emb (traceFormula cRuleDef).val, fun v => by
     simp [Semiformula.eval_emb, cTrace_defined.iff]⟩
 apply (trace.imp cert).orderInduction
 intro n ih
 change modelTrace cRule n → P n
 intro hn
 by_cases hz:n=0
 · subst n; exact zero
 · have hp:0<n := pos_iff_ne_zero.mpr hz
   have he:n=modelListCons (modelListHead n) (modelListTail n) := (modelList_reconstruct n hp).symm
   have ht := modelListTail_lt n hp
   rw [he,modelTrace_cons] at hn
   rw [he]
   exact step _ _ hn.1 (ih _ ht hn.1) hn.2
end ZF192Support.ModelCommands
