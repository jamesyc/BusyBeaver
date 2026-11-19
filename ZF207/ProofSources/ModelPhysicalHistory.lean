module
public import ModelLiteral207Binding
public import ExactTraceModelEquations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def stateCode (s:State M) : M := modelCantor s.q (modelCantor s.left s.right)
def stateGraph : ArithmeticSemisentence 4 :=
 “z q l r. ∃p, !exactCantorGraph p l r ∧ !exactCantorGraph z q p”
lemma stateGraph_eval (z q l r:M) : stateGraph.Evalb ![z,q,l,r] ↔ z=stateCode ⟨q,l,r⟩ := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 simp [stateGraph,stateCode,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Empty.eq_elim,hc]
def codedStep (before after:M) : Prop := ∃s t:State M,
 before=stateCode s ∧ after=stateCode t ∧ literalStep s t
def physicalStepFormula : ArithmeticSemisentence 2 :=
 “before after. ∃q, ∃l, ∃r, ∃q', ∃l', ∃r',
 !stateGraph before q l r ∧ !stateGraph after q' l' r' ∧ !literalStepFormula q l r q' l' r'”
lemma physicalStepFormula_eval (before after:M) : physicalStepFormula.Evalb ![before,after] ↔ codedStep before after := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [physicalStepFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,hv,
 stateGraph_eval,literalStepFormula_eval]
 constructor
 · rintro ⟨q,l,r,ha,q',l',r',hb,he⟩; exact ⟨⟨q,l,r⟩,⟨q',l',r'⟩,ha,hb,he⟩
 · rintro ⟨⟨q,l,r⟩,⟨q',l',r'⟩,ha,hb,he⟩; exact ⟨q,l,r,ha,q',l',r',hb,he⟩
def runEdge (initial next tail:M) : Prop :=
 (tail=0 ∧ next=initial) ∨ (tail≠0 ∧ codedStep (modelListHead tail) next)
def runHistory (initial code:M) : Prop := code≠0 ∧ modelTrace (runEdge initial) code
def physicalRunFormula : ArithmeticSemisentence 2 :=
 “initial n. n≠0 ∧ !tailIterationGraph 0 n n ∧ ∀k<n, ∃g, !tailIterationGraph g k n ∧
 (g=0 ∨ ∃a, ∃b, !listHeadGraph a g ∧ !listTailGraph b g ∧
 ((b=0 ∧ a=initial) ∨ (b≠0 ∧ ∃prev, !listHeadGraph prev b ∧ !physicalStepFormula prev a)))”
lemma physicalRunFormula_eval (initial code:M) :
 physicalRunFormula.Evalb ![initial,code] ↔ runHistory initial code := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [physicalRunFormula,runHistory,runEdge,modelTrace,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,tailIterationGraph_defined.iff,
 ruleHead_defined.iff,ruleTail_defined.iff,physicalStepFormula_eval,eq_comm]
lemma runHistory_singleton (initial:M) : runHistory initial (modelListCons initial 0) := by
 constructor
 · unfold modelListCons; simp
 · rw [modelTrace_cons]; exact ⟨modelTrace_zero _,Or.inl ⟨rfl,rfl⟩⟩
lemma runHistory_extend {initial code next:M} (h:runHistory initial code)
 (hs:codedStep (modelListHead code) next) : runHistory initial (modelListCons next code) := by
 constructor
 · unfold modelListCons; simp
 · rw [modelTrace_cons]; exact ⟨h.2,Or.inr ⟨h.1,hs⟩⟩
noncomputable def blankCode : M := stateCode ⟨0,0,0⟩
def physicalHalts : Prop := ∃hist:M,runHistory blankCode hist ∧ ∀after:M,¬codedStep (modelListHead hist) after
def physicalHaltSentence : ArithmeticSemisentence 0 :=
 “∃initial, ∃hist, ∃last, !stateGraph initial 0 0 0 ∧ !physicalRunFormula initial hist ∧
 !listHeadGraph last hist ∧ ∀after, ¬!physicalStepFormula last after”
lemma physicalHaltSentence_eval : physicalHaltSentence.Evalb (![]:Fin 0→M) ↔ physicalHalts (M:=M) := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [physicalHaltSentence,physicalHalts,blankCode,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,stateGraph_eval,physicalRunFormula_eval,
 ruleHead_defined.iff,physicalStepFormula_eval]
end ZF207.BinaryTape
