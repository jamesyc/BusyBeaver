module
public import I3_380.Search.Compiler.MainSemantics
@[expose] public section

namespace PalomarI3380.Compiler.Source

theorem verifier_empty (e : Equation) (reverse : Bool) (n : Nat) (dict : Fin 3 → Nat) (proposal : Nat) :
    verifyCandidate e reverse n dict 0 proposal = false := by
  simp only [verifyCandidate, acceptMatched]
  cases h : comparePrefix n 0 proposal with
  | none => simp
  | some p =>
    obtain ⟨left, right⟩ := p
    have remains := comparePrefix_incumbent ([] : List Token) h
    have empty : left = 0 := by simpa [encodeTokens] using remains.1
    simp [empty, RawTerm.match_empty]

def CurrentValid (s : SchedulerState) : Prop :=
  s.current = 0 ∨ NumericDerives rows s.current

theorem CurrentValid.begin {s : SchedulerState} (h : CurrentValid s) : CurrentValid s.begin := by
  unfold SchedulerState.begin
  split
  · exact Or.inr .start
  · exact h

theorem mark_valid (e : Equation) (member : e ∈ rows) (s : SchedulerState) (c : TrialInput)
    (h : CurrentValid s) : c.mark e s.current = 0 ∨ NumericDerives rows (c.mark e s.current) := by
  unfold TrialInput.mark
  split
  · rename_i verified
    rcases h with zero | derived
    · have impossible := verifier_empty e (c.orientation != 0) c.position (coordinate c.dictionary) c.proposal
      simp [TrialInput.checked, zero, impossible] at verified
    · exact Or.inr (.next derived member verified)
  · exact Or.inl rfl

theorem iterations_sound {s : SchedulerState} (h : IteratesToHalt main s.store) (valid : CurrentValid s) :
    NumericDerives rows 1 := by
  generalize origin : s.store = start at h
  induction h generalizing s with
  | halt exec =>
    rw [← origin] at exec
    obtain ⟨e, he, p, hp, run⟩ := main_runs s
    have same := (run.deterministic exec).1
    have mark : (TrialInput.decode s.begin.pending).mark e s.begin.current = 1 := by
      unfold trialFlow at same
      split at same <;> simp_all
    have good := mark_valid e he s.begin (TrialInput.decode s.begin.pending) valid.begin
    rw [mark] at good
    exact good.resolve_left (by decide)
  | next exec rest ih =>
    rw [← origin] at exec
    obtain ⟨e, he, p, hp, run⟩ := main_runs s
    let c := TrialInput.decode s.begin.pending
    let m := c.mark e s.begin.current
    have same := run.deterministic exec
    have nonhalt : m ≠ 1 := by
      intro eq
      have agreement : trialFlow m = .normal := same.1
      simp [trialFlow, eq] at agreement
    have validNext : CurrentValid (s.finish p m) := by
      have qualifies := mark_valid e he s.begin c valid.begin
      simpa only [CurrentValid, SchedulerState.finish, nonhalt, ↓reduceIte, m] using qualifies
    exact ih validNext same.2

end PalomarI3380.Compiler.Source
