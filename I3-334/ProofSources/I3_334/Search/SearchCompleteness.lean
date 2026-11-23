module
public import I3_334.Search.TrialCoverage
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open Relation (ReflTransGen)

/-- Every pending attempt eventually exhausts its input unless it halts.
The queue debit is paid even when the proof number is malformed. -/
theorem seek_input (target : Nat) (s : Scheduler) (bound : s.index ≤ target)
    (atTarget : ∀ a : Scheduler, a.index = target → a.pending = 0 → IteratesToHalt main a.store) :
    IteratesToHalt main s.store := by
  induction size : (target - s.index) * (target+1) + s.pending using Nat.strongRecOn generalizing s with
  | ind measure ih =>
    by_cases done : s.index = target ∧ s.pending = 0
    · exact atTarget s done.1 done.2
    · obtain ⟨e,listed,pending,spare,limit,cycle⟩ := run_main s
      let h := TrialHeader.decode s.begin.pending
      let marker := h.mark e s.begin.incumbent
      let next := s.finish pending marker spare
      by_cases stopped : marker = 1
      · exact .halt (by simpa only [marker,h,trialFlow,stopped,↓reduceIte] using cycle)
      · have continuing : Executes main s.store .normal next.store := by
          simpa only [next,trialFlow,marker,h,stopped,↓reduceIte] using cycle
        have decreases : next.index ≤ target ∧
            (target-next.index)*(target+1)+next.pending < measure := by
          by_cases empty : s.pending = 0
          · have before : s.index < target := by omega
            have eq : target-s.index = (target-(s.index+1))+1 := by omega
            have pendingBound : pending ≤ s.index := by
              simpa [Scheduler.begin,empty] using limit
            have measureEq : measure = (target-(s.index+1))*(target+1)+(target+1) := by
              rw [← size,eq,Nat.add_mul,Nat.one_mul,empty,Nat.add_zero]
            simp only [next,Scheduler.finish,Scheduler.begin,empty,↓reduceIte,measureEq]
            exact ⟨by omega,by omega⟩
          · have pendingBound : pending ≤ s.pending-1 := by
              simpa [Scheduler.begin,empty] using limit
            simp only [next,Scheduler.finish,Scheduler.begin,empty,↓reduceIte]
            exact ⟨bound,by omega⟩
        exact .next continuing (ih _ decreases.2 next decreases.1 rfl)

/-- Pack a finite accepting rewrite chain backwards. A continuing
proof suffix is incremented to pay the next iteration's queue debit. -/
theorem encode_chain {old : Nat} (chain : ReflTransGen NumericStep old 1) :
    old = 1 ∨ ∃ word, ∀ s : Scheduler, s.begin.incumbent = old → s.begin.pending = word →
      IteratesToHalt main s.store := by
  refine ReflTransGen.head_induction_on chain ?_ ?_
  · exact Or.inl rfl
  · intro before proposal edge rest ih
    obtain ⟨e,listed,reverse,position,dictionary,accepted⟩ := edge
    rcases ih with done | ⟨following,applyFollowing⟩
    · let input := (encodeHeader e reverse position dictionary proposal 0).encode
      refine Or.inr ⟨input,fun s term pending => ?_⟩
      obtain ⟨_,step⟩ := run_encoded_trial s e listed reverse position dictionary before proposal 0
        accepted pending term
      exact .halt (by simpa only [trialFlow,done,↓reduceIte] using step)
    · by_cases final : proposal = 1
      · let input := (encodeHeader e reverse position dictionary proposal 0).encode
        refine Or.inr ⟨input,fun s term pending => ?_⟩
        obtain ⟨_,step⟩ := run_encoded_trial s e listed reverse position dictionary before proposal 0
          accepted pending term
        exact .halt (by simpa only [trialFlow,final,↓reduceIte] using step)
      · let pending := following+1
        let input := (encodeHeader e reverse position dictionary proposal pending).encode
        refine Or.inr ⟨input,fun s term word => ?_⟩
        obtain ⟨spare,step⟩ := run_encoded_trial s e listed reverse position dictionary before proposal pending
          accepted word term
        let next := s.finish pending proposal spare
        have advance : Executes main s.store .normal next.store := by
          simpa only [next,trialFlow,final,↓reduceIte] using step
        have carries : next.begin.incumbent = proposal := by
          simp [next,Scheduler.finish,Scheduler.begin,pending,final]
        have remaining : next.begin.pending = following := by
          simp [next,Scheduler.finish,Scheduler.begin,pending]
        exact .next advance (applyFollowing next carries remaining)

theorem iterations_complete (chain : ReflTransGen NumericStep 4 1) :
    IteratesToHalt main (fun _ => 0) := by
  have code := encode_chain chain
  rcases code.resolve_left (by decide) with ⟨word,run⟩
  rw [← Scheduler.store_initial]
  apply seek_input word _ (Nat.zero_le word)
  intro s index empty
  apply run s
  · simp [Scheduler.begin,empty]
  · simp [Scheduler.begin,empty,index]

end PalomarI3334.SearchProgram

namespace PalomarI3334

open PalomarI3380 PalomarI3380.Logic

/-- The literal halts precisely when the ten guarded equations derive
the distinguished ground equation. -/
theorem literal_halts_iff_guarded_derivation :
    HaltsFrom machine blank ↔ Derives (.app 1 []) (.app 0 []) := by
  refine ⟨literal_halts_implies_guarded_derivation,?_⟩
  intro derived
  exact literal_halts_iff_search_program.mpr
    (SearchProgram.iterations_complete (numeric_acceptance_iff.mpr derived))

theorem literal_nonhalting_iff_consistency :
    (¬ HaltsFrom machine blank) ↔ ZFCI3Consistent :=
  (not_congr literal_halts_iff_guarded_derivation).trans guarded_underivability_iff_consistency

end PalomarI3334
