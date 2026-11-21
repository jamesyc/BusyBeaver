module
public import I3_380.Search.Compiler.Trie
@[expose] public section

namespace PalomarI3380.Compiler.Source

def matchPiece (dict : Nat) (p : Pattern) (front : Nat) : Option Nat :=
  match p with
  | .side => none
  | .literal t => matchTokens [t] front
  | .variable i => do
    let (word, _) ← readTree (coordinate dict i)
    matchTokens word.tokens front

def matchPattern (dict : Nat) : List Pattern → Nat → Option Nat
  | [], front => some front
  | p :: ps, front => (matchPiece dict p front).bind (matchPattern dict ps)

theorem matchTokens_append (xs ys : List Token) (c : Nat) :
    matchTokens (xs ++ ys) c = (matchTokens xs c).bind (matchTokens ys) := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih =>
    cases h : readToken c with
    | none => simp [matchTokens, h]
    | some pair =>
      obtain ⟨read, tail⟩ := pair
      by_cases same : read = x <;>
        simp [matchTokens, h, same, ih]

theorem matchPattern_append (dict : Nat) (xs ys : List Pattern) (front : Nat) :
    matchPattern dict (xs ++ ys) front = (matchPattern dict xs front).bind (matchPattern dict ys) := by
  induction xs generalizing front with
  | nil => rfl
  | cons p ps ih =>
    cases h : matchPiece dict p front <;> simp [matchPattern, h, ih]

theorem pattern_sides (t : Term (Fin 3)) : .side ∉ pattern t := by
  induction t <;> simp [pattern, *]

private theorem match_tokens_option {front rem : Nat} {token : Token} :
    matchTokens [token] front = some rem ↔ readToken front = some (token, rem) := by
  cases read : readToken front with
  | none => simp [matchTokens, read]
  | some info =>
    rcases info with ⟨head, tail⟩
    by_cases h : head = token <;> simp [matchTokens, read, h]

/-- A marker stays positive exactly when the entire piece matches. On
a successful piece, the physical suffix is the mathematical suffix. -/
structure MatchOutcome (s t : Store) (result : Option Nat) : Prop where
  remainder : ∀ v, result = some v → t fr = v
  marker : t gues ≠ 0 ↔ s gues ≠ 0 ∧ result.isSome = true

theorem piece_outcome (p : Pattern) (s : Store) (hn : p ≠ .side) :
    MatchOutcome s (p.effect s) (matchPiece (s dc) p (s fr)) := by
  cases p with
  | side => exact (hn rfl).elim
  | literal tok =>
    let fields := rawFields (s fr)
    have agreement : ∀ tail, matchTokens [tok] (s fr) = some tail ↔
        tail = fields.rest ∧ tok.arity + 1 = fields.arityField ∧ tok.tag = fields.tag := by
      intro tail
      rw [match_tokens_option]
      constructor
      · intro read
        have remaining : (rawFields (s fr)).rest = tail := by
          rw [← readToken_sound read]
          exact congrArg RawFields.rest (rawFields_encode tok tail)
        refine ⟨remaining.symm, ?_⟩
        have code : readToken (s fr) = some (tok, fields.rest) := by
          change fields.rest = tail at remaining
          rwa [remaining]
        obtain ⟨a, b⟩ := (eatLiteral_effect (s fr) tok).mpr code
        exact ⟨a.symm, b.symm⟩
      · rintro ⟨rfl, a, b⟩
        exact (eatLiteral_effect (s fr) tok).mp ⟨a.symm, b.symm⟩
    have selector : (matchTokens [tok] (s fr)).isSome = true ↔
        tok.arity + 1 = fields.arityField ∧ tok.tag = fields.tag := by
      rw [Option.isSome_iff_exists]
      constructor
      · rintro ⟨r, h⟩
        exact ((agreement r).mp h).2
      · intro h
        exact ⟨fields.rest, (agreement _).mpr ⟨rfl, h⟩⟩
    constructor
    · intro v h
      have hValue : (Pattern.effect (.literal tok) s) fr = fields.rest := by
        simp [Pattern.effect, tokenEffect, fields, Store.set, fr, gues]
      exact hValue.trans ((agreement v).mp h).1.symm
    · change ((s.set fr fields.rest).set gues
        (mark s (tok.arity + 1 = fields.arityField ∧ tok.tag = fields.tag))) gues ≠ 0 ↔
          s gues ≠ 0 ∧ (matchTokens [tok] (s fr)).isSome = true
      rw [Store.get_set, selector]
      unfold mark
      by_cases h : tok.arity + 1 = fields.arityField ∧ tok.tag = fields.tag <;> simp [h]
  | «variable» index =>
    let dict := coordinate (s dc) index
    let result := scanLoop 1 dict (s fr)
    have completeness {v : Nat} (ok : matchPiece (s dc) (.variable index) (s fr) = some v) :
        result.valid = true ∧ result.frontRest = v := by
      change ((readTree dict).bind fun (t, _) => matchTokens t.tokens (s fr)) = some v at ok
      cases read : readTree dict with
      | none => simp [read] at ok
      | some term =>
        rcases term with ⟨t, tail⟩
        simp only [read, Option.bind_some] at ok
        have a := readTree_sound read
        have b := matchTokens_sound ok
        have checked := scanLoop_encoded [t] tail v
        simp only [List.length_cons, List.length_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil] at checked
        rw [a, b] at checked
        change result = _ at checked
        rw [checked]
        exact ⟨rfl, rfl⟩
    have valid : (matchPiece (s dc) (.variable index) (s fr)).isSome = true ↔ result.valid = true := by
      rw [Option.isSome_iff_exists]
      constructor
      · rintro ⟨v, h⟩
        exact (completeness h).1
      · intro h
        obtain ⟨t, read, consumed⟩ := scanLoop_matches dict (s fr) h
        refine ⟨result.frontRest, ?_⟩
        change ((readTree dict).bind fun (t, _) => matchTokens t.tokens (s fr)) = _
        rw [read, Option.bind_some]
        exact consumed
    constructor
    · intro v h
      have value : (Pattern.effect (.variable index) s) fr = result.frontRest := by
        simp [Pattern.effect, dictionaryEffect, result, dict, Store.set, fr, gues]
      exact value.trans (completeness h).2
    · change ((s.set fr result.frontRest).set gues (mark s (result.valid = true))) gues ≠ 0 ↔
        s gues ≠ 0 ∧ (matchPiece (s dc) (.variable index) (s fr)).isSome = true
      rw [Store.get_set, valid]
      unfold mark
      by_cases accepted : result.valid = true <;> simp [accepted]

theorem runPattern_no_side (ps : List Pattern) (s : Store) (h : .side ∉ ps) :
    runPattern ps s lv = s lv ∧ MatchOutcome s (runPattern ps s) (matchPattern (s dc) ps (s fr)) := by
  induction ps generalizing s with
  | nil =>
    exact ⟨rfl, ⟨fun _ h => Option.some.inj h, ⟨fun h₁ => ⟨h₁, rfl⟩, And.left⟩⟩⟩
  | cons p ps ih =>
    have normal : p ≠ .side := fun eq => h (eq ▸ List.mem_cons_self)
    have noSide : .side ∉ ps := fun mem => h (List.mem_cons_of_mem _ mem)
    let t := p.effect s
    have logical := piece_outcome p s normal
    obtain ⟨back, rest⟩ := ih t noSide
    have unchanged : t lv = s lv := by
      cases p with
      | side => exact (normal rfl).elim
      | literal | «variable» => simp [t, Pattern.effect, tokenEffect, dictionaryEffect, Store.set, lv, fr, gues]
    have sameDict : t dc = s dc := p.frame s dc (by decide) (by decide) (by decide)
    refine ⟨back.trans unchanged, ?_⟩
    cases found : matchPiece (s dc) p (s fr) with
    | none =>
      have fail : t gues = 0 := Classical.byContradiction fun h =>
        by simpa [found] using (logical.marker.mp h).2
      constructor
      · intro v hv
        simp [matchPattern, found] at hv
      · constructor
        · intro h
          exact False.elim ((rest.marker.mp h).1 fail)
        · intro h
          simp [matchPattern, found] at h
    | some v =>
      have tail : t fr = v := logical.remainder v found
      simp only [matchPattern, found, Option.bind_some]
      have hRest : matchPattern (t dc) ps (t fr) = matchPattern (s dc) ps v := by rw [sameDict, tail]
      rw [hRest] at rest
      refine ⟨rest.remainder, ?_⟩
      have marked : t gues ≠ 0 ↔ s gues ≠ 0 := logical.marker.trans (by simp [found])
      exact rest.marker.trans (and_congr_left' marked)

end PalomarI3380.Compiler.Source
