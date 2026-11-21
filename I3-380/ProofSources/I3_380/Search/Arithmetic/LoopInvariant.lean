module
public import I3_380.Search.Arithmetic.CounterPrograms
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PalomarI3380.Arithmetic (Chain)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Build the loop trace from a definable invariant. This supports
model-finite loop lengths even when no explicit state formula is given. -/
theorem coded_while_invariant (r : Register) (body : Program) (count start : M)
    (I : M → M → Prop) (definition : 𝚺ᴬ₁-Relation I) (initial : I 0 start)
    (iterate : ∀ i < count, ∀ state : M, I i state →
      Store.ofCode state r ≠ 0 ∧
        ∃ next : M, body.Runs .normal
          (Store.writeCode r state (Store.ofCode state r-1)) next ∧ I (i+1) next)
    (ready : ∀ state : M, I count state → Store.ofCode state r = 0) :
    ∃ finish, (whilePositive r body).Runs .normal start finish ∧ I count finish := by
  let suffix := Program.seq body (continue_ 1)
  let edge := fun a b : M => ∃ m, (dec r).Runs .normal a m ∧ suffix.Runs (.repeatAt 0) m b
  have units := (dec r).runs_definable (M := M) .normal
  have loops := suffix.runs_definable (M := M) (.repeatAt 0)
  have definableEdge : 𝚺ᴬ₁-Relation edge := by unfold edge; definability
  have definableTrace : 𝚺ᴬ₁-Relation₃ (Chain edge) := by unfold Chain; definability
  have beforeExit (i : M) : i ≤ count → ∃ state, Chain edge i start state ∧ I i state := by
    induction i using ISigma1.sigma1_succ_induction with
    | zero => intro _; exact ⟨start,Chain.refl edge start,initial⟩
    | succ i smaller =>
      intro inRange
      have earlier := succ_le_iff_lt.mp inRange
      obtain ⟨state,trace,invariant⟩ := smaller (le_of_lt earlier)
      obtain ⟨positive,next,payload,preserved⟩ := iterate i earlier state invariant
      have consume : (dec r).Runs .normal state (Store.writeCode r state (Store.ofCode state r-1)) :=
        Or.inr ⟨rfl,positive,rfl⟩
      have back : (continue_ 1).Runs (.repeatAt 1) next next := ⟨rfl,rfl⟩
      have returns : suffix.Runs (.repeatAt 0) (Store.writeCode r state (Store.ofCode state r-1)) next :=
        Program.Runs.rightExit payload back rfl
      exact ⟨next,trace.trans (Chain.single ⟨_,consume,returns⟩),preserved⟩
    | hP => definability
  obtain ⟨finish,trace,invariant⟩ := beforeExit count le_rfl
  have stop : (dec r).Runs (.escape 0) finish finish := Or.inl ⟨rfl,ready finish invariant,rfl⟩
  exact ⟨finish,⟨count,finish,trace,Or.inl stop⟩,invariant⟩

/-- Full arithmetic supplies induction for loops whose interior
counter can grow, provided a definable measure strictly decreases. -/
theorem coded_while_measure [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (r : Register) (body : Program) (measure : M → M)
    (measureDef : 𝚺ᴬ₁-Function₁ measure) (I : M → Prop) (invariantDef : 𝚺ᴬ₁-Predicate I)
    (advance : ∀ state : M, I state → Store.ofCode state r ≠ 0 →
      ∃ next : M, body.Runs .normal
        (Store.writeCode r state (Store.ofCode state r-1)) next ∧
        I next ∧ measure next < measure state) :
    ∀ start : M, I start → ∃ finish : M,
      (whilePositive r body).Runs .normal start finish ∧ I finish ∧ Store.ofCode finish r = 0 := by
  let result := fun start : M => ∃ finish : M,
    (whilePositive r body).Runs .normal start finish ∧ I finish ∧ Store.ofCode finish r = 0
  have runs := (whilePositive r body).runs_definable (M := M) .normal
  have read := Store.read_definable (M := M) r
  have resultDef : 𝚺ᴬ₁-Predicate result := by unfold result; definability
  let P := fun m : M => ∀ state : M, measure state ≤ m → I state → result state
  have invariantSigma : 𝚺ᴬ_[2]-Predicate I := .of_lt invariantDef (by decide)
  have resultPi : 𝚷ᴬ_[2]-Predicate result := .of_lt resultDef (by decide)
  have measureBound : 𝚺ᴬ₁-Relation (fun state m => measure state ≤ m) := by definability
  have boundSigma : 𝚺ᴬ_[2]-Relation (fun state m => measure state ≤ m) := .of_lt measureBound (by decide)
  have pred : 𝚷ᴬ_[2]-Predicate P := by
    change 𝚷ᴬ_[2].Definable (fun v : Fin 1 → M => ∀ state : M, measure state ≤ v 0 → I state → result state)
    apply Bounding.HierarchySymbol.Definable.all
    exact Bounding.HierarchySymbol.Definable.imp boundSigma
      (Bounding.HierarchySymbol.Definable.imp (invariantSigma.retraction (fun _ => 0))
        (resultPi.retraction (fun _ => 0)))
  have complete : ∀ n : M, P n := by
    apply InductionOnHierarchy.order_induction_sigma 𝚷 2 pred
    intro bound smaller state admissible invariant
    by_cases stop : Store.ofCode state r = 0
    · have exit : (dec r).Runs (.escape 0) state state := Or.inl ⟨rfl,stop,rfl⟩
      exact ⟨state,Program.Runs.leftExit exit rfl,invariant,stop⟩
    · obtain ⟨next,run,nextInvariant,decreases⟩ := advance state invariant stop
      obtain ⟨endState,tail,done,zero⟩ :=
        smaller (measure next) (lt_of_lt_of_le decreases admissible) next le_rfl nextInvariant
      have consume : (dec r).Runs .normal state (Store.writeCode r state (Store.ofCode state r-1)) :=
        Or.inr ⟨rfl,stop,rfl⟩
      have again : (continue_ 1).Runs (.repeatAt 1) next next := ⟨rfl,rfl⟩
      have loop := Program.Runs.rightExit run again (out := .repeatAt 0) rfl
      exact ⟨endState,Program.Runs.reenter consume loop tail,done,zero⟩
  intro start invariant
  exact complete (measure start) start le_rfl invariant

end PalomarI3380.Compiler.Source
