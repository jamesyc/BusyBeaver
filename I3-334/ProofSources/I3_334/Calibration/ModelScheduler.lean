module
public import I3_334.Calibration.ModelSchedulerTrial
public import I3_334Support.Arithmetic.SchedulerMeasure
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (schedulerBudget schedulerBudget_definable schedulerBudget_tail
  schedulerBudget_next definableAllCons)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def schedulerCode (index pending current scratchWord : M) : M :=
  (Scheduler.mk index pending current scratchWord).store.code

theorem schedulerCode_definable : 𝚺ᴬ₁-Function₄ (schedulerCode (M := M)) := by
  letI := Store.writeCode_definable (M := M) np
  letI := Store.writeCode_definable (M := M) pl
  letI := Store.writeCode_definable (M := M) fr
  letI := Store.writeCode_definable (M := M) tmp
  have shape (n p g t : M) : schedulerCode n p g t =
      Store.writeCode tmp (Store.writeCode fr (Store.writeCode pl
        (Store.writeCode np (Store.code (fun _ => (0 : M))) n) p) g) t := by
    simp [schedulerCode,Scheduler.store,Store.writeCode]
  change 𝚺ᴬ₁.Definable (fun v : Fin 5 → M => v 0 = schedulerCode (v 1) (v 2) (v 3) (v 4))
  simp only [shape]
  definability

set_option maxHeartbeats 1500000 in
/-- Every positive pending word is eventually tried with a reset
current word, unless a trial has already halted. -/
theorem coded_seek [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (target : M)
    (success : ∀ current scratchWord, CodedTermination (schedulerCode target 0 current scratchWord)) :
    ∀ s : Scheduler M, s.index ≤ target → s.pending ≤ target → CodedTermination s.store.code := by
  let P := fun budget : M => ∀ n p g t : M, n ≤ target → p ≤ target →
    schedulerBudget target n p = budget → CodedTermination (schedulerCode n p g t)
  letI code : 𝚺ᴬ_[2]-Function₄ (schedulerCode (M := M)) :=
    (schedulerCode_definable (M := M)).of_lt (by decide)
  have terminates : 𝚷ᴬ_[2]-Predicate (CodedTermination (M := M)) :=
    (codedTermination_definable (M := M)).of_lt (by decide)
  have compare : 𝚺ᴬ_[2]-Function₂ (schedulerBudget target) :=
    (schedulerBudget_definable target).of_lt (by decide)
  have aCode : 𝚷ᴬ_[2]-Predicate P := by
    have idx : 𝚺ᴬ_[2].Definable (fun v : Fin 5 → M => v 3 ≤ target) := by definability
    have pending : 𝚺ᴬ_[2].Definable (fun v : Fin 5 → M => v 2 ≤ target) := by definability
    have comparison : 𝚺ᴬ_[2].Definable (fun v : Fin 3 → M => v 0 = schedulerBudget target (v 1) (v 2)) := compare
    have budget : 𝚺ᴬ_[2].Definable (fun v : Fin 5 → M => schedulerBudget target (v 3) (v 2) = v 4) :=
      (comparison.retraction (![4,3,2] : Fin 3 → Fin 5)).of_iff (fun _ => eq_comm)
    have run : 𝚷ᴬ_[2].Definable (fun v : Fin 5 → M => CodedTermination (schedulerCode (v 3) (v 2) (v 1) (v 0))) := by
      exact terminates.comp (Bounding.HierarchySymbol.DefinableFunction₄.comp (.var 3) (.var 2) (.var 1) (.var 0))
    have typed := idx.imp (Γ := 𝚷) (pending.imp (Γ := 𝚷) (budget.imp (Γ := 𝚷) run))
    exact definableAllCons (definableAllCons (definableAllCons (definableAllCons typed)))
  have all := InductionOnHierarchy.order_induction_sigma 𝚷 2 aCode (fun budget ih => by
    intro n p g t indexBound pendingBound equals
    let s : Scheduler M := ⟨n,p,g,t⟩
    by_cases empty : p=0
    · subst p
      rcases lt_or_eq_of_le indexBound with before | rfl
      · rcases coded_main_total s with stopped | ⟨q,limit,c,u,normal⟩
        · exact stopped
        · have nextBound : q ≤ n := by simpa [s,Scheduler.begin] using limit
          have new := schedulerBudget_next target n q before (nextBound.trans indexBound)
          have decreasing : schedulerBudget target (n+1) q < budget := new.trans_eq equals
          have stops := ih _ decreasing (n+1) q c u (succ_le_iff_lt.mpr before)
            (nextBound.trans indexBound) rfl
          have normalized : main.Runs .normal (schedulerCode n 0 g t) (schedulerCode (n+1) q c u) := by
            simpa [s,Scheduler.begin,schedulerCode] using normal
          exact stops.prepend normalized
      · exact success g t
    · rcases coded_main_total s with stopped | ⟨q,limit,c,u,normal⟩
      · exact stopped
      · have nextBound : q ≤ p-1 := by simpa [s,Scheduler.begin,empty] using limit
        have positive : 0 < p := lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm empty)
        have earlier : p-1 < p := by
          rcases zero_or_succ p with z | ⟨k,eq⟩
          · exact (empty z).elim
          · rw [eq,Arithmetic.add_sub_self]
            exact lt_add_one _
        have decreasing := (schedulerBudget_tail target n (nextBound.trans_lt earlier)).trans_eq equals
        have stops := ih _ decreasing n q c u indexBound ((le_of_lt (nextBound.trans_lt earlier)).trans pendingBound) rfl
        have normalized : main.Runs .normal (schedulerCode n p g t) (schedulerCode n q c u) := by
          simpa [s,Scheduler.begin,empty,schedulerCode] using normal
        exact stops.prepend normalized)
  intro s index pending
  exact all (schedulerBudget target s.index s.pending) s.index s.pending s.incumbent s.scratchWord index pending rfl

end PalomarI3334.SearchProgram
