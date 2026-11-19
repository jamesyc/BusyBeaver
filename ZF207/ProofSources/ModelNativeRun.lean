module
public import ModelNativeHistory
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeSource
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def nativeRunEdge (initial next tail:M) : Prop :=
 (tail=0 ∧ next=initial) ∨ (tail≠0 ∧ codedStep (modelListHead tail) next)
def nativeRunHistory (initial code:M) : Prop := code≠0 ∧ modelTrace (nativeRunEdge initial) code
noncomputable def nativeRunFormula : ArithmeticSemiformula Nat 2 :=
 “initial n. n≠0 ∧ !tailIterationGraph 0 n n ∧ ∀k<n, ∃g, !tailIterationGraph g k n ∧
 (g=0 ∨ ∃a, ∃b, !listHeadGraph a g ∧ !listTailGraph b g ∧
 ((b=0 ∧ a=initial) ∨ (b≠0 ∧ ∃prev, !listHeadGraph prev b ∧ !nativeStepFormula prev a)))”
lemma nativeRunFormula_eval (ρ:Nat→M) (initial code:M) :
 nativeRunFormula.Eval ![initial,code] ρ ↔ nativeRunHistory initial code := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [nativeRunFormula,nativeRunHistory,nativeRunEdge,modelTrace,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,tailIterationGraph_defined.iff,
 ruleHead_defined.iff,ruleTail_defined.iff,nativeStepFormula_eval,eq_comm]
lemma nativeRunHistory_singleton (initial:M) : nativeRunHistory initial (modelListCons initial 0) := by
 constructor
 · unfold modelListCons; simp
 · rw [modelTrace_cons]; exact ⟨modelTrace_zero _,Or.inl ⟨rfl,rfl⟩⟩
lemma nativeRunHistory_extend {initial code next:M} (h:nativeRunHistory initial code)
 (hs:codedStep (modelListHead code) next) : nativeRunHistory initial (modelListCons next code) := by
 constructor
 · unfold modelListCons; simp
 · rw [modelTrace_cons]; exact ⟨h.2,Or.inr ⟨h.1,hs⟩⟩
end ZF207.NativeSource
