module
public import I3_380.Search.Compiler.SearchSoundness
@[expose] public section

namespace PalomarI3380.Compiler.Source

/-- Every pending trial is eventually exhausted, unless it halts first.
Consequently every requested input word is reached by the scheduler. -/
theorem seek_input (target : Nat) (s : SchedulerState) (bound : s.nextWord ≤ target)
    (atTarget : ∀ (a : SchedulerState), a.nextWord = target → a.pending = 0 →
      IteratesToHalt main a.store) :
    IteratesToHalt main s.store := by
  induction measureEq : (target - s.nextWord) * (target + 1) + s.pending
      using Nat.strongRecOn generalizing s with
  | ind measure ih =>
    by_cases done : s.nextWord = target ∧ s.pending = 0
    · exact atTarget s done.1 done.2
    · obtain ⟨eqn, member, p, limit, exec⟩ := main_runs s
      let c := TrialInput.decode s.begin.pending
      let marker := c.mark eqn s.begin.current
      let next := s.finish p marker
      by_cases stopped : marker = 1
      · exact .halt (by simpa only [marker, c, trialFlow, stopped, ↓reduceIte] using exec)
      · have continues : Executes main s.store .normal next.store := by
          simpa only [trialFlow, marker, c, stopped, ↓reduceIte] using exec
        have tail : p ≤ s.begin.pending :=
          Nat.le_trans limit (TrialInput.pending_le _)
        have step : ∀ (b : SchedulerState), b = next →
            b.nextWord ≤ target ∧ (target - b.nextWord) * (target + 1) + b.pending < measure := by
          intro b hb
          subst b
          by_cases pendingZero : s.pending = 0
          · have index : s.nextWord < target := by omega
            have eq : target - s.nextWord = (target - (s.nextWord + 1)) + 1 := by omega
            have hp : p ≤ s.nextWord := by simpa [SchedulerState.begin, pendingZero] using tail
            have hMeasure : measure = (target - (s.nextWord + 1)) * (target + 1) + (target + 1) := by
              rw [← measureEq, eq, Nat.add_mul, Nat.one_mul, pendingZero, Nat.add_zero]
            simp only [next, SchedulerState.finish, SchedulerState.begin, pendingZero, ↓reduceIte,
              hMeasure]
            exact ⟨by omega, by omega⟩
          · have hp : p ≤ s.pending - 1 := by simpa [SchedulerState.begin, pendingZero] using tail
            simp only [next, SchedulerState.finish, SchedulerState.begin, pendingZero, ↓reduceIte]
            exact ⟨bound, by omega⟩
        have ⟨index, smaller⟩ := step next rfl
        exact .next continues (ih _ smaller next index rfl)

/-- Rewrite evidence in the order in which the input stream must be read. -/
inductive NumericPath (E : List Equation) : Nat → Nat → Prop where
  | done (word : Nat) : NumericPath E word word
  | take {e : Equation} {before after final : Nat} {reverse : Bool} {position : Nat} {dict : Fin 3 → Nat} :
      e ∈ E → verifyCandidate e reverse position dict before after = true →
      NumericPath E after final → NumericPath E before final

theorem NumericPath.add_last {E : List Equation} {old last new : Nat} {e : Equation} {reverse : Bool}
    {position : Nat} {dict : Fin 3 → Nat} (chain : NumericPath E old last) (member : e ∈ E)
    (eqn : verifyCandidate e reverse position dict last new = true) :
    NumericPath E old new := by
  induction chain with
  | done => exact .take member eqn (.done _)
  | take mem proof _ ih => exact .take mem proof (ih eqn)

theorem NumericDerives.path {E : List Equation} {n : Nat} (derivation : NumericDerives E n) :
    NumericPath E 4 n := by
  induction derivation with
  | start => exact .done _
  | next _ member proof ih => exact ih.add_last member proof

set_option maxHeartbeats 4000000 in
theorem NumericPath.encoded {old final : Nat} (p : NumericPath rows old final)
    (last : final = 1) (startNotHalt : old ≠ 1) :
    ∃ word, ∀ (s : SchedulerState), s.begin.current = old → s.begin.pending = word →
      IteratesToHalt main s.store := by
  induction p with
  | done => exact (startNotHalt last).elim
  | @take e before after final reverse position dict member accepts path ih =>
    let input : TrialInput := ⟨after, position, if reverse then 1 else 0, encodeDictionary dict, 0⟩
    obtain ⟨selectors, verifiedRun⟩ := main_covers member
    let encode := fun suffix => ({input with pending := encodeFields selectors suffix} : TrialInput).encode
    have verified : input.checked e before = true := by
      unfold TrialInput.checked
      have coordinateEq : coordinate (encodeDictionary dict) = dict := funext (coordinate_encode dict)
      simp only [input, coordinateEq]
      cases reverse <;> exact accepts
    have marker (s : SchedulerState) (old : s.begin.current = before) : input.mark e s.begin.current = after := by
      rw [old, TrialInput.mark, verified]
      rfl
    by_cases isLast : after = 1
    · refine ⟨encode 0, fun s old code => ?_⟩
      have step := verifiedRun s input 0 code
      rw [marker s old, isLast] at step
      exact .halt step
    · obtain ⟨following, rest⟩ := ih last isLast
      let pending := following + 1
      refine ⟨encode pending, fun s old code => ?_⟩
      have step := verifiedRun s input pending code
      rw [marker s old] at step
      let next := s.finish pending after
      have step' : Executes main s.store .normal next.store := by
        simpa only [trialFlow, isLast, ↓reduceIte] using step
      have nextOld : next.begin.current = after := by
        simp [next, SchedulerState.finish, SchedulerState.begin, pending, isLast]
      have nextCode : next.begin.pending = following := by
        simp [next, SchedulerState.finish, SchedulerState.begin, pending]
      exact .next step' (rest next nextOld nextCode)

theorem iterations_complete (proof : NumericDerives rows 1) :
    IteratesToHalt main (fun _ => 0) := by
  obtain ⟨input, script⟩ := (NumericDerives.path proof).encoded rfl (by decide)
  rw [← SchedulerState.store_initial]
  apply seek_input input _ (Nat.zero_le input)
  intro s reached empty
  apply script s
  · simp [SchedulerState.begin, empty]
  · simp [SchedulerState.begin, empty, reached]

theorem exact_machine_halts_iff_derives :
    HaltsFrom machine blank ↔ Derives Manifest.final (.const .D) (.const .J) := by
  rw [literal_halts_iff_source]
  constructor
  · intro h
    have eq := SchedulerState.store_initial
    rw [← eq] at h
    obtain ⟨term, code, same⟩ := (iterations_sound h (Or.inl rfl)).sound
    have target : term = singleConstant .J := by
      have hCode : term.encode = (singleConstant .J).encode := code.trans rawCode_J.symm
      have read := congrArg readTree hCode
      simp only [RawTerm.encode, readTree_complete, Option.some.injEq, Prod.mk.injEq] at read
      exact read.1
    apply Derives.complete
    intro A M model
    have agreement := same A M ((source_models_iff M).mpr model)
    rw [target, evaluate_singleConstant] at agreement
    exact agreement.symm
  · intro proof
    apply iterations_complete
    rw [← rawCode_J]
    exact NumericDerives.of_chain (source_derives_iff.mpr proof).rewriteChain

end PalomarI3380.Compiler.Source
