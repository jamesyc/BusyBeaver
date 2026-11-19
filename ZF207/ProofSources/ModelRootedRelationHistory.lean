module
public import ModelCommandTotality
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelScheduler
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def rootedEdge (R:M→M→Prop) (initial next tail:M) : Prop :=
 (tail=0 ∧ next=initial) ∨ (tail≠0 ∧ R (modelListHead tail) next)
def rooted (R:M→M→Prop) (initial code:M) : Prop := code≠0 ∧ modelTrace (rootedEdge R initial) code
def rootedFormula (rel:ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 2 :=
 “initial n. n≠0 ∧ !tailIterationGraph 0 n n ∧ ∀k<n, ∃g, !tailIterationGraph g k n ∧
 (g=0 ∨ ∃a, ∃b, !listHeadGraph a g ∧ !listTailGraph b g ∧
 ((b=0 ∧ a=initial) ∨ (b≠0 ∧ ∃prev, !listHeadGraph prev b ∧ !rel prev a)))”
lemma rootedFormula_eval (rel:ArithmeticSemiformula Nat 2) (ρ:Nat→M) (R:M→M→Prop)
 (hr:∀a b,rel.Eval ![a,b] ρ ↔ R a b) (initial code:M) :
 (rootedFormula rel).Eval ![initial,code] ρ ↔ rooted R initial code := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [rootedFormula,rooted,rootedEdge,modelTrace,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,tailIterationGraph_defined.iff,
 ruleHead_defined.iff,ruleTail_defined.iff,hr,eq_comm]
lemma rooted_singleton (R:M→M→Prop) (initial:M) : rooted R initial (modelListCons initial 0) := by
 constructor
 · unfold modelListCons; simp
 · rw [modelTrace_cons]; exact ⟨modelTrace_zero _,Or.inl ⟨rfl,rfl⟩⟩
lemma rooted_extend (R:M→M→Prop) {initial code next:M} (h:rooted R initial code)
 (hs:R (modelListHead code) next) : rooted R initial (modelListCons next code) := by
 constructor
 · unfold modelListCons; simp
 · rw [modelTrace_cons]; exact ⟨h.2,Or.inr ⟨h.1,hs⟩⟩
end ZF207.ModelScheduler
