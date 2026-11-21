module
public import I3_380.Search.Compiler.MainInput
public import I3_380.Search.Compiler.MainOutput
@[expose] public section

namespace PalomarI3380.Compiler.Source

theorem comparePrefix_swap (n a b : Nat) :
    comparePrefix n b a = (comparePrefix n a b).map Prod.swap := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [comparePrefix]
    let x := rawFields a
    let y := rawFields b
    by_cases yes : x.arityField = y.arityField ∧ x.tag = y.tag
    · have reverse : y.arityField = x.arityField ∧ y.tag = x.tag := ⟨yes.1.symm, yes.2.symm⟩
      rw [ite_eq_left reverse, ite_eq_left yes]
      exact ih x.rest y.rest
    · have reverse : ¬(y.arityField = x.arityField ∧ y.tag = x.tag) :=
        fun h => yes ⟨h.1.symm, h.2.symm⟩
      rw [ite_eq_right reverse, ite_eq_right yes]
      rfl

theorem verifyCandidate_swap (e : Equation) (n : Nat) (dict : Fin 3 → Nat) (old new : Nat) :
    verifyCandidate e true n dict old new = verifyCandidate e false n dict new old := by
  simp only [verifyCandidate, oriented, Bool.false_eq_true, ↓reduceIte, acceptMatched]
  rw [comparePrefix_swap n old new]
  cases front : comparePrefix n old new with
  | none => rfl
  | some rest =>
    obtain ⟨a, b⟩ := rest
    simp only [Option.map_some, Prod.swap]
    cases matchTokens (Term.toRaw (dictionaryTerm dict) e.2).tokens a <;>
    cases matchTokens (Term.toRaw (dictionaryTerm dict) e.1).tokens b <;> simp [BEq.comm]

theorem Pattern.marker_falls (p : Pattern) (s : Store) :
    p.effect s gues = s gues ∨ p.effect s gues = 0 := by
  cases p with
  | side =>
    exact Or.inl (by simp [Pattern.effect, Store.set, gues, lv, fr])
  | literal t =>
    simp only [Pattern.effect, tokenEffect, Store.get_set, mark]
    split <;> simp
  | «variable» i =>
    simp only [Pattern.effect, dictionaryEffect, Store.get_set, mark]
    split <;> simp

theorem runPattern_marker_falls (ps : List Pattern) (s : Store) :
    runPattern ps s gues = s gues ∨ runPattern ps s gues = 0 := by
  induction ps generalizing s with
  | nil => exact Or.inl rfl
  | cons p ps ih =>
    change runPattern ps (p.effect s) gues = s gues ∨ runPattern ps (p.effect s) gues = 0
    rcases ih (p.effect s) with same | zero
    · rw [same]
      exact p.marker_falls s
    · exact Or.inr zero

theorem remainingMarker_nonzero (s : Store) :
    remainingMarker s ≠ 0 ↔ s gues ≠ 0 ∧ s fr = s lv := by
  simp only [remainingMarker, mark]
  by_cases h : s fr = s lv <;> simp [h]

theorem row_marker_value (eqn : Equation) (s : Store) :
    remainingMarker (runPattern (rowPattern eqn) s) =
      if suffixMatch eqn (s dc) (s fr) (s lv) then s gues else 0 := by
  let result := runPattern (rowPattern eqn) s
  have guard : remainingMarker result ≠ 0 ↔ s gues ≠ 0 ∧ suffixMatch eqn (s dc) (s fr) (s lv) = true :=
    (remainingMarker_nonzero result).trans (row_marker eqn s)
  have bounded : remainingMarker result = s gues ∨ remainingMarker result = 0 := by
    unfold remainingMarker mark
    split
    · exact runPattern_marker_falls _ _
    · exact Or.inr rfl
  by_cases ok : suffixMatch eqn (s dc) (s fr) (s lv) = true
  · simp only [ok, ↓reduceIte]
    rcases bounded with same | zero
    · exact same
    · have first : s gues = 0 := Classical.byContradiction fun absent => (guard.mpr ⟨absent, ok⟩) zero
      exact zero.trans first.symm
  · simp only [ok]
    exact Classical.byContradiction fun ne => ok (guard.mp ne).2

def TrialInput.checked (c : TrialInput) (eqn : Equation) (current : Nat) : Bool :=
  verifyCandidate eqn (c.orientation != 0) c.position (coordinate c.dictionary) current c.proposal

def TrialInput.mark (c : TrialInput) (eqn : Equation) (current : Nat) : Nat :=
  if c.checked eqn current then c.proposal else 0

set_option maxHeartbeats 3500000 in
theorem prepared_row_marker (c : TrialInput) (eqn : Equation) (s : SchedulerState) :
    remainingMarker (runPattern (rowPattern eqn) (c.prepare s)) = c.mark eqn s.current := by
  rw [row_marker_value]
  let result := prefixSummary c.position s.current c.proposal
  have prefixEq : comparePrefix c.position s.current c.proposal =
      if result.1 then some result.2 else none :=
    prefixSummary_correct _ _ _
  by_cases orientation : c.orientation = 0
  · have checked : c.checked eqn s.current = if result.1 then
        suffixMatch eqn c.dictionary result.2.1 result.2.2 else false := by
      rw [TrialInput.checked]
      have dir : (c.orientation != 0) = false := by simp [orientation]
      rw [dir, suffixMatch_verifier, prefixEq]
      cases result.1 <;> simp
    simp only [TrialInput.prepare, orientation, ↓reduceIte, TrialInput.prefix, TrialInput.mark, checked]
    by_cases flag : (prefixSummary c.position s.current c.proposal).1 = true <;>
      simp [stageStore, Store.set, fr, lv, dc, gues, result, flag]
  · have checked : c.checked eqn s.current = if result.1 then
        suffixMatch eqn c.dictionary result.2.2 result.2.1 else false := by
      rw [TrialInput.checked]
      have dir : (c.orientation != 0) = true := by simp [orientation]
      rw [dir, verifyCandidate_swap, suffixMatch_verifier, comparePrefix_swap, prefixEq]
      cases result.1 <;> simp [Prod.swap]
    simp only [TrialInput.prepare, orientation, ↓reduceIte, TrialInput.prefix, TrialInput.mark, checked]
    by_cases flag : (prefixSummary c.position s.current c.proposal).1 = true <;>
      simp [stageStore, Store.set, fr, lv, dc, gues, result, flag]

theorem remainingMarker_controls (s : Store) (pending selector : Nat) :
    remainingMarker (controls s pending selector) = remainingMarker s := by
  simp [remainingMarker, mark, controls, Store.set, pl, sel, fr, lv, gues]
  rfl

theorem TrialInput.prepare_pending (c : TrialInput) (s : SchedulerState) (pending : Nat) :
    ({ c with pending := pending } : TrialInput).prepare s = controls (c.prepare s) pending 0 := by
  by_cases direction : c.orientation = 0 <;>
    (apply store_ext <;>
      simp [TrialInput.prepare, TrialInput.prefix, direction, stageStore, controls,
        SchedulerState.store, emptyStore, Store.set, pl, sel, fr, lv, gues, dc, np, goal] <;> rfl)

theorem TrialInput.pending_le (word : Nat) : (decode word).pending ≤ word := by
  have tail_le (n : Nat) : (Cantor.unpair n).2 ≤ n := by
    have h := Cantor.right_le (Cantor.unpair n).1 (Cantor.unpair n).2
    rwa [Cantor.pair_unpair] at h
  dsimp only [decode]
  exact Nat.le_trans (tail_le _) (Nat.le_trans (tail_le _) (Nat.le_trans (tail_le _) (tail_le _)))

end PalomarI3380.Compiler.Source
