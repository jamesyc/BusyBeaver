module
public import ModelCommandParse
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def runEdge (initial next tail:M) : Prop :=
 (tail=0 ∧ next=initial) ∨ (tail≠0 ∧ codedCommandStep (modelListHead tail) next)
def runHistory (initial code:M) : Prop := code≠0 ∧ modelTrace (runEdge initial) code
noncomputable def runFormula : ArithmeticSemiformula Nat 2 :=
 “initial n. n≠0 ∧ !tailIterationGraph 0 n n ∧ ∀k<n, ∃g, !tailIterationGraph g k n ∧
 (g=0 ∨ ∃a, ∃b, !listHeadGraph a g ∧ !listTailGraph b g ∧
 ((b=0 ∧ a=initial) ∨ (b≠0 ∧ ∃prev, !listHeadGraph prev b ∧ !commandStepFormula prev a)))”
lemma runFormula_eval (ρ:Nat→M) (initial code:M) :
 runFormula.Eval ![initial,code] ρ ↔ runHistory initial code := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [runFormula,runHistory,runEdge,modelTrace,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,tailIterationGraph_defined.iff,
 ruleHead_defined.iff,ruleTail_defined.iff,commandStepFormula_eval,eq_comm]
lemma runHistory_singleton (initial:M) : runHistory initial (modelListCons initial 0) := by
 constructor
 · unfold modelListCons; simp
 · rw [modelTrace_cons]; exact ⟨modelTrace_zero _,Or.inl ⟨rfl,rfl⟩⟩
lemma runHistory_extend {initial code next:M} (h:runHistory initial code)
 (hs:codedCommandStep (modelListHead code) next) : runHistory initial (modelListCons next code) := by
 constructor
 · unfold modelListCons; simp
 · rw [modelTrace_cons]; exact ⟨h.2,Or.inr ⟨h.1,hs⟩⟩
/-- Halt means executing SHIFT fails; it is not exhausted residual pointer zero. -/
def haltAt (code:M) : Prop := ∃(tail:M) (s:Store M),
 code=commandCfgCode (commandCode .shift tail+1) s ∧ s.t+s.h=1
noncomputable def haltFormula : ArithmeticSemiformula Nat 1 :=
 “n. ∃tail, ∃pc, ∃s, ∃t, ∃w, ∃d, ∃h,
 !exactCantorGraph pc 0 tail ∧ !storeGraph s t w d h ∧
 !exactCantorGraph n (pc+1) s ∧ t+h=1”
lemma haltFormula_eval (ρ:Nat→M) (code:M) : haltFormula.Eval ![code] ρ ↔ haltAt code := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [haltFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,
 Empty.eq_elim,hc,storeGraph_eval]
 constructor
 · rintro ⟨tail,t,w,d,h,he,hh⟩; exact ⟨tail,⟨t,w,d,h⟩,he,hh⟩
 · rintro ⟨tail,⟨t,w,d,h⟩,he,hh⟩; exact ⟨tail,t,w,d,h,he,hh⟩
end ZF207.ModelCommands
