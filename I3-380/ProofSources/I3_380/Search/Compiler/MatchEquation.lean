module
public import I3_380.Search.Compiler.MatchPatterns
@[expose] public section

namespace PalomarI3380.Compiler.Source

def pieceValid (dict : Nat) : Pattern → Bool
  | .side => false
  | .literal _ => true
  | .variable i => (readTree (coordinate dict i)).isSome

def pieceTokens (dict : Nat) : Pattern → List Token
  | .side => []
  | .literal t => [t]
  | .variable i => (dictionaryTerm (coordinate dict) i).tokens

theorem matchPiece_expand (dict : Nat) (p : Pattern) (front : Nat) :
    matchPiece dict p front =
      if pieceValid dict p then matchTokens (pieceTokens dict p) front else none := by
  cases p with
  | side => rfl
  | literal => rfl
  | «variable» i =>
    cases read : readTree (coordinate dict i) with
    | none => simp [pieceValid, matchPiece, read]
    | some term =>
      rcases term with ⟨t, tail⟩
      simp [pieceValid, matchPiece, read, pieceTokens, dictionaryTerm]

theorem matchPattern_expand (dict : Nat) (ps : List Pattern) (front : Nat) :
    matchPattern dict ps front =
      if ps.all (pieceValid dict) then matchTokens (ps.flatMap (pieceTokens dict)) front else none := by
  induction ps generalizing front with
  | nil => rfl
  | cons p ps ih =>
    simp only [matchPattern, matchPiece_expand, List.all_cons, List.flatMap_cons, matchTokens_append]
    cases hp : pieceValid dict p
    · simp
    · cases found : matchTokens (pieceTokens dict p) front
      · simp
      · cases hs : ps.all (pieceValid dict) <;> simp [ih, hs]

theorem pattern_valid (dict : Nat) (t : Term (Fin 3)) :
    (pattern t).all (pieceValid dict) = t.variables.all fun i => (readTree (coordinate dict i)).isSome := by
  induction t <;>
    simp only [pattern, pieceValid, Term.variables, List.all_cons, List.all_nil, List.all_append,
      Bool.true_and, Bool.and_true, *]

theorem pattern_tokens (dict : Nat) (t : Term (Fin 3)) :
    (pattern t).flatMap (pieceTokens dict) = (t.toRaw (dictionaryTerm (coordinate dict))).tokens := by
  induction t <;>
    simp only [pattern, pieceTokens, Term.toRaw, RawTerm.tokens_app, List.length_cons, List.length_nil,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
      List.append_nil, List.append_assoc, *]

theorem matchPattern_term (dict : Nat) (t : Term (Fin 3)) (front : Nat) :
    matchPattern dict (pattern t) front =
      if t.variables.all (fun i => (readTree (coordinate dict i)).isSome) then
        matchTokens (t.toRaw (dictionaryTerm (coordinate dict))).tokens front else none := by
  rw [matchPattern_expand, pattern_valid, pattern_tokens]

/-- Compatibility of the two sides when a successful match leaves the
same untouched suffix on both words. -/
def suffixMatch (eqn : Equation) (dict front back : Nat) : Bool :=
  match matchPattern dict (pattern eqn.1) front, matchPattern dict (pattern eqn.2) back with
  | some l, some r => l == r
  | _, _ => false

theorem suffixMatch_verifier (eqn : Equation) (dict pos old proposal : Nat) :
    verifyCandidate eqn false pos (coordinate dict) old proposal =
      match comparePrefix pos old proposal with
      | some (front, back) => suffixMatch eqn dict front back
      | none => false := by
  simp only [verifyCandidate, oriented, Bool.false_eq_true, ↓reduceIte, dictionaryValid, List.all_append,
    acceptMatched]
  cases prefixEq : comparePrefix pos old proposal with
  | none => simp
  | some pair =>
    rcases pair with ⟨front, back⟩
    simp only [suffixMatch, matchPattern_term]
    cases h₁ : eqn.1.variables.all (fun i => (readTree (coordinate dict i)).isSome) <;>
    cases h₂ : eqn.2.variables.all (fun i => (readTree (coordinate dict i)).isSome) <;>
    simp
    all_goals
      cases matchTokens (eqn.1.toRaw (dictionaryTerm (coordinate dict))).tokens front <;>
      cases matchTokens (eqn.2.toRaw (dictionaryTerm (coordinate dict))).tokens back <;> simp

theorem runPattern_scratch (pattern : List Pattern) (s : Store) (clear : ClearScratch s) :
    ClearScratch (runPattern pattern s) := by
  induction pattern generalizing s with
  | nil => exact clear
  | cons p ps ih => exact ih _ (p.ready clear)

theorem runPattern_dict (pattern : List Pattern) (s : Store) :
    runPattern pattern s dc = s dc := by
  induction pattern generalizing s with
  | nil => rfl
  | cons p ps ih =>
    exact (ih (p.effect s)).trans (p.frame s dc (by decide) (by decide) (by decide))

/-- The compiled equation row compares the two instantiated sides.
The final marker has its incoming value precisely on a valid match with
equal suffixes. This includes candidates whose marker was already zero. -/
theorem row_marker (eqn : Equation) (s : Store) :
    let out := runPattern (rowPattern eqn) s
    (out gues ≠ 0 ∧ out fr = out lv) ↔
      s gues ≠ 0 ∧ suffixMatch eqn (s dc) (s fr) (s lv) = true := by
  dsimp only
  rw [rowPattern, List.append_assoc, runPattern_append]
  let left := runPattern (pattern eqn.1) s
  let mid := Pattern.effect .side left
  let out := runPattern (pattern eqn.2) mid
  change (out gues ≠ 0 ∧ out fr = out lv) ↔ _
  obtain ⟨back, leftMatch⟩ := runPattern_no_side (pattern eqn.1) s (pattern_sides _)
  obtain ⟨rightBack, rightMatch⟩ := runPattern_no_side (pattern eqn.2) mid (pattern_sides _)
  have midFr : mid fr = s lv := by
    change ((left.set fr (left lv)).set lv (left fr)) fr = s lv
    rw [Store.get_set_other _ _ _ _ (by decide : fr ≠ lv), Store.get_set]
    exact back
  have midLv : mid lv = left fr := Store.get_set _ _ _
  have midGuess : mid gues = left gues := by simp [mid, Pattern.effect, Store.set, fr, lv, gues]
  have dict : mid dc = s dc :=
    (Pattern.frame .side left dc (by decide) (by decide) (by decide)).trans (runPattern_dict _ s)
  change MatchOutcome mid out (matchPattern (mid dc) (pattern eqn.2) (mid fr)) at rightMatch
  rw [dict, midFr] at rightMatch
  unfold suffixMatch
  cases hLeft : matchPattern (s dc) (pattern eqn.1) (s fr) with
  | none =>
    simp only [hLeft] at leftMatch
    have absent : left gues = 0 := Classical.byContradiction fun h => by
      have no := (leftMatch.marker.mp h).2
      contradiction
    constructor
    · rintro ⟨marked, _⟩
      exact ((rightMatch.marker.mp marked).1 (midGuess.trans absent)).elim
    · rintro ⟨_, h⟩
      cases hRight : matchPattern (s dc) (pattern eqn.2) (s lv) <;> simp_all
  | some l =>
    have first : left fr = l := leftMatch.remainder l hLeft
    have markerLeft : left gues ≠ 0 ↔ s gues ≠ 0 :=
      leftMatch.marker.trans (by simp [hLeft])
    have outBack : out lv = l := rightBack.trans (midLv.trans first)
    cases hRight : matchPattern (s dc) (pattern eqn.2) (s lv) with
    | none =>
      constructor
      · rintro ⟨marked, _⟩
        have no := (rightMatch.marker.mp marked).2
        simp [hRight] at no
      · rintro ⟨_, h⟩
        simp at h
    | some r =>
      have markerRight : out gues ≠ 0 ↔ s gues ≠ 0 :=
        rightMatch.marker.trans (by simp [hRight, midGuess, markerLeft])
      have outFront : out fr = r := rightMatch.remainder r hRight
      rw [outBack, outFront, markerRight]
      exact and_congr_right fun _ => (beq_iff_eq.trans eq_comm).symm

end PalomarI3380.Compiler.Source
