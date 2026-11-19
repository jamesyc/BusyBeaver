module
public import ModelAppendGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelOperationalConcat
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def boundedFormula (φ:ArithmeticSemiformula Nat 1) : ArithmeticSemiformula Nat 1 :=
 “n. ∀ y<n, !φ y”
lemma boundedFormula_eval (φ:ArithmeticSemiformula Nat 1) (ρ:Nat→M) (P:M→Prop)
 (hP:∀n,φ.Eval ![n] ρ ↔ P n) (n:M) :
 (boundedFormula φ).Eval ![n] ρ ↔ ∀y<n,P y := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [boundedFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,hP]
lemma pa_order_induction (φ:ArithmeticSemiformula Nat 1) (ρ:Nat→M) (P:M→Prop)
 (hP:∀n,φ.Eval ![n] ρ ↔ P n)
 (step:∀n,(∀m<n,P m)→P n) : ∀n,P n := by
 haveI : M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
  models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔)
 have allBounded : ∀n:M,∀m<n,P m := by
  refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n:M=>∀m<n,P m) ?_ ?_ ?_
  · exact ⟨ρ,boundedFormula φ,by trivial,fun n=>(boundedFormula_eval φ ρ P hP n).symm⟩
  · intro m hm; exact False.elim (not_lt_zero hm)
  · intro n ih m hm
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hm) with hlt|heq
    · exact ih m hlt
    · subst m; exact step n ih
 intro n
 exact allBounded (n+1) n (by simp)
lemma model_list_induction (φ:ArithmeticSemiformula Nat 1) (ρ:Nat→M) (P:M→Prop)
 (hP:∀n,φ.Eval ![n] ρ ↔ P n) (zero:P 0)
 (cons:∀a b,P b→P (modelListCons a b)) : ∀n,P n := by
 apply pa_order_induction φ ρ P hP
 intro n ih
 by_cases hn:n=0
 · simpa only [hn] using zero
 · have hp:=pos_iff_ne_zero.mpr hn
   rw [←modelList_reconstruct n hp]
   exact cons _ _ (ih _ (modelListTail_lt n hp))
end ZF207.ModelOperationalConcat
