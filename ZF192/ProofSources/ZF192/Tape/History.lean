module
public import ZF192.Tape.LiteralBinding
public import ZF192Support.Coding.Histories.Rooted
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
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
 simp [physicalStepFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,Matrix.constant_eq_singleton,
 stateGraph_eval,literalStepFormula_eval]
 constructor
 · rintro ⟨q,l,r,ha,q',l',r',hb,he⟩; exact ⟨⟨q,l,r⟩,⟨q',l',r'⟩,ha,hb,he⟩
 · rintro ⟨⟨q,l,r⟩,⟨q',l',r'⟩,ha,hb,he⟩; exact ⟨q,l,r,ha,q',l',r',hb,he⟩
abbrev runEdge (initial next tail : M) : Prop :=
  ZF192Support.ModelScheduler.rootedEdge codedStep initial next tail
abbrev runHistory (initial code : M) : Prop :=
  ZF192Support.ModelScheduler.rooted codedStep initial code
def physicalRunFormula : ArithmeticSemisentence 2 :=
  ZF192Support.ModelScheduler.rootedFormula physicalStepFormula
lemma physicalRunFormula_eval (initial code : M) :
    physicalRunFormula.Evalb ![initial, code] ↔ runHistory initial code :=
  ZF192Support.ModelScheduler.rootedFormula_eval physicalStepFormula Empty.elim codedStep
    physicalStepFormula_eval initial code
lemma runHistory_singleton (initial : M) : runHistory initial (modelListCons initial 0) :=
  ZF192Support.ModelScheduler.rooted_singleton codedStep initial
lemma runHistory_extend {initial code next : M} (h : runHistory initial code)
    (hs : codedStep (modelListHead code) next) : runHistory initial (modelListCons next code) :=
  ZF192Support.ModelScheduler.rooted_extend codedStep h hs

noncomputable def blankCode : M := stateCode ⟨0,0,0⟩
def physicalHalts : Prop := ∃hist:M,runHistory blankCode hist ∧ ∀after:M,¬codedStep (modelListHead hist) after
def physicalHaltSentence : ArithmeticSemisentence 0 :=
 “∃initial, ∃hist, ∃last, !stateGraph initial 0 0 0 ∧ !physicalRunFormula initial hist ∧
 !listHeadGraph last hist ∧ ∀after, ¬!physicalStepFormula last after”
lemma physicalHaltSentence_eval : physicalHaltSentence.Evalb (![]:Fin 0→M) ↔ physicalHalts (M:=M) := by
 simp [physicalHaltSentence,physicalHalts,blankCode,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,Empty.eq_elim,stateGraph_eval,physicalRunFormula_eval,
 ruleHead_defined.iff,physicalStepFormula_eval]
end ZF192.BinaryTape
