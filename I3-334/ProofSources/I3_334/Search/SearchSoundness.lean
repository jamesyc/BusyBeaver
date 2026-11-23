module
public import I3_334.Search.MainTrial
public import I3_334.Proof.InternalArithmetic
public import I3_334.Proof.EquationalConsistency
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open Templates (equations)
open Relation (ReflTransGen)

theorem run_main (s : Scheduler) :
    ∃ (e : Templates.Equation), e ∈ equations ∧
      ∃ pending scratchWord, pending ≤ s.begin.pending ∧
        let mark := (TrialHeader.decode s.begin.pending).mark e s.begin.incumbent
        Executes main s.store (trialFlow mark) (s.finish pending mark scratchWord).store := by
  let h := TrialHeader.decode s.begin.pending
  let start := TrieInput s.begin h
  obtain ⟨e,listed,after,run,ready,view,tails⟩ := rows_run start (TrieInput.scratch _ _)
  have tail : start pl = h.selectors := by
    simp [start,TrieInput,Store.set,pl,fr,lv,dc,gues]
  rw [tail] at tails
  exact ⟨e,listed,after pl,after tmp,tails.trans (TrialHeader.selectors_le _),
    finish_trial s e after run ready view⟩

theorem checker_empty (h : TrialHeader) (e : Templates.Equation) :
    h.check e 0 = false := by
  unfold TrialHeader.check checkTrial acceptMatched
  cases hit : comparePrefix h.position 0 h.proposal with
  | none => rfl
  | some fronts =>
    obtain ⟨left,right⟩ := fronts
    have previous := comparePrefix_incumbent ([] : List Token) hit
    have noOld : left = 0 := by
      simpa [encodeTokens] using previous.1
    simp [noOld,RawTerm.match_empty]

def ValidIncumbent (s : Scheduler) : Prop :=
  s.incumbent = 0 ∨ ReflTransGen NumericStep 4 s.incumbent

theorem ValidIncumbent.begin {s : Scheduler} (valid : ValidIncumbent s) : ValidIncumbent s.begin := by
  unfold Scheduler.begin
  split
  · exact Or.inr .refl
  · exact valid

theorem valid_mark {s : Scheduler} (valid : ValidIncumbent s)
    (e : Templates.Equation) (listed : e ∈ equations) (h : TrialHeader) :
    h.mark e s.incumbent = 0 ∨ ReflTransGen NumericStep 4 (h.mark e s.incumbent) := by
  unfold TrialHeader.mark markedIf
  split
  · rename_i verified
    rcases valid with empty | known
    · rw [empty,checker_empty h e] at verified
      contradiction
    · exact Or.inr (known.tail ⟨e,listed,h.reverse,h.position,h.dictionary,verified⟩)
  · exact Or.inl rfl

theorem iterations_sound {s : Scheduler}
    (halting : IteratesToHalt main s.store) (valid : ValidIncumbent s) :
    ReflTransGen NumericStep 4 1 := by
  generalize origin : s.store = start at halting
  induction halting generalizing s with
  | halt actual =>
    rw [← origin] at actual
    obtain ⟨e,listed,tail,scratch,_,trace⟩ := run_main s
    have same := (trace.deterministic actual).1
    let h := TrialHeader.decode s.begin.pending
    have mark : h.mark e s.begin.incumbent = 1 := by
      unfold trialFlow at same
      split at same <;> simp_all [h]
    have verified := valid_mark valid.begin e listed h
    rw [mark] at verified
    exact verified.resolve_left (by decide)
  | next cycle next ih =>
    rw [← origin] at cycle
    obtain ⟨e,listed,tail,scratch,_,trace⟩ := run_main s
    let h := TrialHeader.decode s.begin.pending
    let mark := h.mark e s.begin.incumbent
    have same := trace.deterministic cycle
    have carries : mark ≠ 1 := by
      intro stopped
      have wrong : trialFlow mark = .normal := same.1
      simp [trialFlow,stopped] at wrong
    have validNext : ValidIncumbent (s.finish tail mark scratch) := by
      have known := valid_mark valid.begin e listed h
      simpa only [ValidIncumbent,Scheduler.finish,carries,↓reduceIte,mark] using known
    exact ih validNext same.2

end PalomarI3334.SearchProgram

namespace PalomarI3334

open PalomarI3380 PalomarI3380.Logic

theorem literal_halts_implies_guarded_derivation (halted : HaltsFrom machine blank) :
    Derives (.app 1 []) (.app 0 []) := by
  have run := literal_halts_iff_search_program.mp halted
  rw [← SearchProgram.Scheduler.store_initial] at run
  exact numeric_acceptance_iff.mp (SearchProgram.iterations_sound run (Or.inl rfl))

theorem literal_nonhalting_of_consistency (consistent : ZFCI3Consistent) : ¬ HaltsFrom machine blank :=
  fun halt => (guarded_underivability_of_consistency consistent) (literal_halts_implies_guarded_derivation halt)

theorem literal_halting_unprovable (soundness : ArithmeticSigma1Sound) :
    ¬ ZFCI3Provable haltingSentence :=
  halting_unprovable_of_nonhalting soundness (literal_nonhalting_of_consistency soundness.consistent)

end PalomarI3334
