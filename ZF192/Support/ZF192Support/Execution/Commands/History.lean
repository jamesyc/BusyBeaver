module
public import ZF192Support.Execution.Commands.Parse
public import ZF192Support.Coding.Histories.Rooted
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
abbrev runEdge (initial next tail : M) : Prop :=
  ZF192Support.ModelScheduler.rootedEdge codedCommandStep initial next tail
abbrev runHistory (initial code : M) : Prop :=
  ZF192Support.ModelScheduler.rooted codedCommandStep initial code
noncomputable def runFormula : ArithmeticSemiformula Nat 2 :=
  ZF192Support.ModelScheduler.rootedFormula commandStepFormula
lemma runFormula_eval (ρ : Nat → M) (initial code : M) :
    runFormula.Eval ![initial, code] ρ ↔ runHistory initial code :=
  ZF192Support.ModelScheduler.rootedFormula_eval commandStepFormula ρ codedCommandStep
    (commandStepFormula_eval ρ) initial code
lemma runHistory_singleton (initial : M) : runHistory initial (modelListCons initial 0) :=
  ZF192Support.ModelScheduler.rooted_singleton codedCommandStep initial
lemma runHistory_extend {initial code next : M} (h : runHistory initial code)
    (hs : codedCommandStep (modelListHead code) next) : runHistory initial (modelListCons next code) :=
  ZF192Support.ModelScheduler.rooted_extend codedCommandStep h hs

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
 simp [haltFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,
 Empty.eq_elim,hc,storeGraph_eval]
 constructor
 · rintro ⟨tail,t,w,d,h,he,hh⟩; exact ⟨tail,⟨t,w,d,h⟩,he,hh⟩
 · rintro ⟨tail,⟨t,w,d,h⟩,he,hh⟩; exact ⟨tail,t,w,d,h,he,hh⟩
end ZF192Support.ModelCommands
