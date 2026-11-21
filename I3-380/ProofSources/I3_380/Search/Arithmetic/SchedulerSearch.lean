module
public import I3_380.Search.Arithmetic.TrialPrograms
public import I3_380.Search.Arithmetic.SourceIteration
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem coded_main_total [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (s : SchedulerState M) :
    CodedTermination s.store.code ∨
      ∃ p ≤ s.begin.pending, ∃ g : M,
        main.Runs .normal s.store.code (SchedulerState.mk s.begin.nextWord p g).store.code := by
  let c := TrialInput.modelDecode s.begin.pending
  obtain ⟨a,b,g,input⟩ := coded_input_total s
  let start := c.modelPrepare s.begin a b g
  have ready := c.modelPrepare_scratch s.begin a b g
  obtain ⟨front,back,marker,p,r,limit,row⟩ := coded_rows start ready
  let out := controls (replaceContext start front back marker) p r
  let g' := remainingMarker out
  have outReady : ClearScratch out := (ready.context_state _ _ _).controls _ _
  have executed := coded_trial s input row outReady
  have index : out np = s.begin.nextWord := by
    unfold out start TrialInput.modelPrepare
    split <;>
      simp [controls,replaceContext,stageStore,SchedulerState.store,Store.set,np,pl,sel,goal,fr,lv,gues,dc]
  have kept : out pl=p := controls_pl ..
  have read : start pl=c.pending := c.modelPrepare_pending _ _ _ _
  have bound : p ≤ s.begin.pending := (limit.trans_eq read).trans (TrialInput.modelDecode_pending_le _)
  have actual : main.Runs (if g'=1 then .halt else .normal) s.store.code
      (SchedulerState.mk s.begin.nextWord p (if g'=1 then 0 else g')).store.code := by
    have h : main.Runs (if g'=1 then .halt else .normal) s.store.code
        (SchedulerState.mk (out np) (out pl) (if g'=1 then 0 else g')).store.code := executed
    rwa [index,kept] at h
  by_cases accepted : g'=1
  · exact Or.inl (.of_halt (by simpa only [accepted,↓reduceIte] using actual))
  · exact Or.inr ⟨p,bound,g',by simpa only [accepted,↓reduceIte] using actual⟩

noncomputable def schedulerCode (index pending current : M) : M :=
  (SchedulerState.mk index pending current).store.code

theorem schedulerCode_definable : 𝚺ᴬ₁-Function₃ (schedulerCode (M := M)) := by
  have index := Store.writeCode_definable (M := M) np
  have pending := Store.writeCode_definable (M := M) pl
  have current := Store.writeCode_definable (M := M) goal
  have code (n p g : M) : schedulerCode n p g =
      Store.writeCode goal (Store.writeCode pl (Store.writeCode np (emptyStore : Store M).code n) p) g := by
    simp [schedulerCode,SchedulerState.store,Store.writeCode]
  change 𝚺ᴬ₁.Definable (fun v : Fin 4 → M => v 0 = schedulerCode (v 1) (v 2) (v 3))
  simp only [code]
  definability

noncomputable def schedulerBudget (target index pending : M) : M :=
  (target-index)*(target+1)+pending

theorem schedulerBudget_tail (target index : M) {p q : M} (smaller : q < p) :
    schedulerBudget target index q < schedulerBudget target index p := by
  unfold schedulerBudget
  exact add_lt_add_right smaller _

theorem schedulerBudget_next (target index p : M) (before : index < target) (bound : p ≤ target) :
    schedulerBudget target (index+1) p < schedulerBudget target index 0 := by
  unfold schedulerBudget
  have needed : index+1 ≤ target := succ_le_iff_lt.mpr before
  have remainder : target-(index+1)+1=target-index := by
    apply add_right_cancel (b := index)
    calc
      target-(index+1)+1+index = target-(index+1)+(index+1) := by ac_rfl
      _ = target := tsub_add_cancel_of_le needed
      _ = target-index+index := (tsub_add_cancel_of_le (le_of_lt before)).symm
  rw [← remainder,add_mul,one_mul,add_zero]
  exact add_lt_add_right (lt_of_le_of_lt bound (lt_add_one _)) _

theorem schedulerBudget_definable (target : M) : 𝚺ᴬ₁-Function₂ (schedulerBudget target) := by
  unfold schedulerBudget
  definability

theorem definableAllCons {n k : Nat} {P : (Fin (n+1) → M) → Prop}
    (h : 𝚷ᴬ_[k+1].Definable P) : 𝚷ᴬ_[k+1].Definable (fun v => ∀ x, P (x :> v)) := by
  exact Bounding.HierarchySymbol.Definable.all (P := fun v x => P (x :> v)) (h.of_iff fun _ => by simp)

set_option maxHeartbeats 1500000 in
/-- Every positive pending word is eventually tried with a reset
current word, unless a trial has already halted. -/
theorem coded_seek [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (target : M)
    (success : ∀ current, CodedTermination (schedulerCode target 0 current)) :
    ∀ s : SchedulerState M, s.nextWord ≤ target → s.pending ≤ target → CodedTermination s.store.code := by
  let P := fun budget : M => ∀ n p g : M, n ≤ target → p ≤ target →
    schedulerBudget target n p = budget → CodedTermination (schedulerCode n p g)
  letI code : 𝚺ᴬ_[2]-Function₃ (schedulerCode (M := M)) :=
    (schedulerCode_definable (M := M)).of_lt (by decide)
  have terminates : 𝚷ᴬ_[2]-Predicate (CodedTermination (M := M)) :=
    (codedTermination_definable (M := M)).of_lt (by decide)
  have compare : 𝚺ᴬ_[2]-Function₂ (schedulerBudget target) :=
    (schedulerBudget_definable target).of_lt (by decide)
  have aCode : 𝚷ᴬ_[2]-Predicate P := by
    have idx : 𝚺ᴬ_[2].Definable (fun v : Fin 4 → M => v 2 ≤ target) := by definability
    have pending : 𝚺ᴬ_[2].Definable (fun v : Fin 4 → M => v 1 ≤ target) := by definability
    have comparison : 𝚺ᴬ_[2].Definable (fun v : Fin 3 → M => v 0 = schedulerBudget target (v 1) (v 2)) := compare
    have budget : 𝚺ᴬ_[2].Definable (fun v : Fin 4 → M => schedulerBudget target (v 2) (v 1) = v 3) :=
      (comparison.retraction (![3,2,1] : Fin 3 → Fin 4)).of_iff (fun _ => eq_comm)
    have run : 𝚷ᴬ_[2].Definable (fun v : Fin 4 → M => CodedTermination (schedulerCode (v 2) (v 1) (v 0))) := by
      exact terminates.comp (Bounding.HierarchySymbol.DefinableFunction₃.comp (.var 2) (.var 1) (.var 0))
    have typed := idx.imp (Γ := 𝚷) (pending.imp (Γ := 𝚷) (budget.imp (Γ := 𝚷) run))
    exact definableAllCons (definableAllCons (definableAllCons typed))
  have all := InductionOnHierarchy.order_induction_sigma 𝚷 2 aCode (fun budget ih => by
    intro n p g indexBound pendingBound equals
    let s : SchedulerState M := ⟨n,p,g⟩
    by_cases empty : p=0
    · subst p
      rcases lt_or_eq_of_le indexBound with before | rfl
      · rcases coded_main_total s with stopped | ⟨q,limit,c,normal⟩
        · exact stopped
        · have nextBound : q ≤ n := by simpa [s,SchedulerState.begin] using limit
          have new := schedulerBudget_next target n q before (nextBound.trans indexBound)
          have decreasing : schedulerBudget target (n+1) q < budget := new.trans_eq equals
          have stops := ih _ decreasing (n+1) q c (succ_le_iff_lt.mpr before)
            (nextBound.trans indexBound) rfl
          have normalized : main.Runs .normal (schedulerCode n 0 g) (schedulerCode (n+1) q c) := by
            simpa [s,SchedulerState.begin,schedulerCode] using normal
          exact stops.prepend normalized
      · exact success g
    · rcases coded_main_total s with stopped | ⟨q,limit,c,normal⟩
      · exact stopped
      · have nextBound : q ≤ p-1 := by simpa [s,SchedulerState.begin,empty] using limit
        have positive : 0 < p := lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm empty)
        have earlier : p-1 < p := by
          rcases zero_or_succ p with z | ⟨k,eq⟩
          · exact (empty z).elim
          · rw [eq,Arithmetic.add_sub_self]
            exact lt_add_one _
        have decreasing := (schedulerBudget_tail target n (nextBound.trans_lt earlier)).trans_eq equals
        have stops := ih _ decreasing n q c indexBound ((le_of_lt (nextBound.trans_lt earlier)).trans pendingBound) rfl
        have normalized : main.Runs .normal (schedulerCode n p g) (schedulerCode n q c) := by
          simpa [s,SchedulerState.begin,empty,schedulerCode] using normal
        exact stops.prepend normalized)
  intro s index pending
  exact all (schedulerBudget target s.nextWord s.pending) s.nextWord s.pending s.current index pending rfl

end PalomarI3380.Compiler.Source
