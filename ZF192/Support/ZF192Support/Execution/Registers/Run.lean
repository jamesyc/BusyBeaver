module
public import ZF192Support.Execution.Registers.History
public import ZF192Support.Coding.Histories.Rooted
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeSource
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
abbrev nativeRunEdge (initial next tail : M) : Prop :=
  ZF192Support.ModelScheduler.rootedEdge codedStep initial next tail
abbrev nativeRunHistory (initial code : M) : Prop :=
  ZF192Support.ModelScheduler.rooted codedStep initial code
noncomputable def nativeRunFormula : ArithmeticSemiformula Nat 2 :=
  ZF192Support.ModelScheduler.rootedFormula nativeStepFormula
lemma nativeRunFormula_eval (ρ : Nat → M) (initial code : M) :
    nativeRunFormula.Eval ![initial, code] ρ ↔ nativeRunHistory initial code :=
  ZF192Support.ModelScheduler.rootedFormula_eval nativeStepFormula ρ codedStep
    (nativeStepFormula_eval ρ) initial code
lemma nativeRunHistory_singleton (initial : M) : nativeRunHistory initial (modelListCons initial 0) :=
  ZF192Support.ModelScheduler.rooted_singleton codedStep initial
lemma nativeRunHistory_extend {initial code next : M} (h : nativeRunHistory initial code)
    (hs : codedStep (modelListHead code) next) : nativeRunHistory initial (modelListCons next code) :=
  ZF192Support.ModelScheduler.rooted_extend codedStep h hs

/-- Reachability in a coded source history, at any PA-model register values. -/
def nativeReaches (s t:State M) : Prop := ∀initial hist:M,
 nativeRunHistory initial hist → modelListHead hist=stateCode s →
 ∃out:M,nativeRunHistory initial out ∧ modelListHead out=stateCode t
lemma nativeReaches_step {s t:State M} (h:programStep s t) : nativeReaches s t := by
 intro initial hist hr hh
 refine ⟨modelListCons (stateCode t) hist,?_,modelListHead_cons _ _⟩
 apply nativeRunHistory_extend hr
 rw [hh]; exact ⟨s,t,rfl,rfl,h⟩
lemma nativeReaches_trans {s t u:State M} (a:nativeReaches s t) (b:nativeReaches t u) : nativeReaches s u := by
 intro initial hist hr hh
 obtain ⟨out,ho,he⟩:=a initial hist hr hh
 exact b initial out ho he

end ZF192Support.NativeSource
