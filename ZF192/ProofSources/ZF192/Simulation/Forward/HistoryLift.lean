module
public import ZF192Support.Execution.Registers.Run
public import ZF192.Tape.History
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.NativePhysicalLift
open ZFR.ArithmeticRepresentation ZF192Support.NativeSource
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Relation is on coded native/physical states. Its physical witness can carry
changing gap/spare values, not a fixed hidden resource invariant. -/
def StepContract (R:M→M→Prop) : Prop := ∀a b p:M,codedStep a b→R a p→
 ∀root hist:M,BinaryTape.runHistory root hist→modelListHead hist=p→
 ∃out q:M,BinaryTape.runHistory root out ∧ modelListHead out=q ∧ R b q
def Simulation (R:M→M→Prop) (initial code:M) : Prop := nativeRunHistory initial code→
 ∀root hist p:M,BinaryTape.runHistory root hist→modelListHead hist=p→R initial p→
 ∃out q:M,BinaryTape.runHistory root out ∧ modelListHead out=q ∧ R (modelListHead code) q
noncomputable def simulationFormula (relation:ArithmeticSemisentence 2) : ArithmeticSemiformula Nat 1 :=
 “code. !nativeRunFormula &0 code → ∀root, ∀hist, ∀p,
 (!BinaryTape.physicalRunFormula root hist ∧ !listHeadGraph p hist ∧ !relation &0 p) →
 ∃out, ∃q, ∃last, !BinaryTape.physicalRunFormula root out ∧ !listHeadGraph q out ∧
 !listHeadGraph last code ∧ !relation last q”
lemma simulationFormula_eval (relation:ArithmeticSemisentence 2) (R:M→M→Prop)
 (hr:∀a b,relation.Evalb ![a,b]↔R a b) (ρ:Nat→M) (code:M) :
 (simulationFormula relation).Eval ![code] ρ ↔ Simulation R (ρ 0) code := by
 simp [simulationFormula,Simulation,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,Empty.eq_elim,nativeRunFormula_eval,
 BinaryTape.physicalRunFormula_eval,ruleHead_defined.iff,hr,eq_comm]
/-- Lift every model-internal register history using the first-order step invariant. -/
theorem native_history_lift (relation : ArithmeticSemisentence 2) (R : M → M → Prop)
    (hr : ∀ a b, relation.Evalb ![a, b] ↔ R a b) (hs : StepContract R) (initial : M) :
    ∀ code : M, Simulation R initial code := by
  refine ZF192Support.ModelScheduler.rooted_induction codedStep initial
    (simulationFormula relation) (fun _ => initial)
    (fun last => ∀ root hist p, BinaryTape.runHistory root hist →
      modelListHead hist = p → R initial p →
        ∃ out q, BinaryTape.runHistory root out ∧ modelListHead out = q ∧ R last q)
    (simulationFormula_eval relation R hr (fun _ => initial)) ?_ ?_
  · intro _ hist p hhist hhead hrel
    exact ⟨hist, p, hhist, hhead, hrel⟩
  · intro before after hstep ih root hist p hhist hhead hrel
    obtain ⟨mid, q, hmid, hq, hrq⟩ := ih root hist p hhist hhead hrel
    exact hs before after q hstep hrq root mid hmid hq
end ZF192.NativePhysicalLift
