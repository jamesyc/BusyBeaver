module
public import I3_380.Search.Contexts
@[expose] public section

namespace PalomarI3380

/-- The raw two-field pop used by the context loop, with 0 permitted
as a biased arity. An exhausted word pops as three zeros. -/
structure RawFields where
  arityField : Nat
  tag : Nat
  rest : Nat

def rawFields (code : Nat) : RawFields :=
  let first := Cantor.unpair code
  let second := Cantor.unpair first.2
  ⟨first.1, second.1, second.2⟩

theorem rawFields_encode (tok : Token) (tail : Nat) :
    rawFields (Cantor.pair (tok.arity + 1) (Cantor.pair tok.tag tail)) =
      ⟨tok.arity + 1, tok.tag, tail⟩ := by
  simp only [rawFields, Cantor.unpair_pair]

theorem rawFields_rebuild (code : Nat) :
    let r := rawFields code
    Cantor.pair r.arityField (Cantor.pair r.tag r.rest) = code := by
  simp only [rawFields, Cantor.pair_unpair]

theorem rawFields_zero : rawFields 0 = ⟨0, 0, 0⟩ := rfl

def comparePrefix : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, left, right => some (left, right)
  | n + 1, left, right =>
    let a := rawFields left
    let b := rawFields right
    if a.arityField = b.arityField ∧ a.tag = b.tag then comparePrefix n a.rest b.rest else none

theorem comparePrefix_encoded (xs : List Token) (left right : Nat) :
    comparePrefix xs.length (encodeTokens xs left) (encodeTokens xs right) = some (left, right) := by
  induction xs with
  | nil => rfl
  | cons tok xs ih =>
    simpa only [List.length_cons, encodeTokens, comparePrefix, rawFields_encode, true_and,
      ↓reduceIte] using ih

/-- On a canonical incumbent, a successful common-prefix scan either
consumes a genuine prefix or exhausts the incumbent. -/
theorem comparePrefix_incumbent {n proposed a b : Nat} (xs : List Token)
    (h : comparePrefix n (encodeTokens xs 0) proposed = some (a, b)) :
    a = encodeTokens (xs.drop n) 0 ∧
      (n ≤ xs.length → proposed = encodeTokens (xs.take n) b) := by
  induction n generalizing xs proposed a b with
  | zero =>
    simp only [comparePrefix, Option.some.injEq, Prod.mk.injEq] at h
    simpa only [List.drop_zero, List.take_zero, encodeTokens] using
      And.intro h.1.symm (fun _ : 0 ≤ xs.length => h.2)
  | succ n ih =>
    cases xs with
    | nil =>
      simp only [comparePrefix] at h
      split at h
      · have hRest : (rawFields (encodeTokens [] 0)).rest = 0 := rfl
        rw [hRest] at h
        obtain ⟨hl, _⟩ := ih [] h
        exact ⟨by simpa only [List.drop_nil] using hl, fun bound => by simp at bound⟩
      · contradiction
    | cons tok xs =>
      simp only [encodeTokens, comparePrefix, rawFields_encode] at h
      split at h
      next eq =>
        obtain ⟨hl, hr⟩ := ih xs h
        refine ⟨hl, ?_⟩
        intro bound
        have hRest := hr (by simp only [List.length_cons] at bound; omega)
        have hCode := rawFields_rebuild proposed
        simp only at hCode
        simp only [List.take_succ_cons, encodeTokens]
        rw [← hRest, eq.1, eq.2]
        exact hCode.symm
      next _ => contradiction

def matchTokens : List Token → Nat → Option Nat
  | [], code => some code
  | expected :: pattern, code => do
    let (actual, rest) ← readToken code
    if actual = expected then matchTokens pattern rest else none

theorem matchTokens_encoded (ts : List Token) (tail : Nat) :
    matchTokens ts (encodeTokens ts tail) = some tail := by
  induction ts with
  | nil => rfl
  | cons tok ts ih =>
    have h := readToken_encode tok (encodeTokens ts tail)
    simp [matchTokens, encodeTokens, h, ih]

theorem matchTokens_sound {ts : List Token} {code tail : Nat}
    (h : matchTokens ts code = some tail) : encodeTokens ts tail = code := by
  induction ts generalizing code with
  | nil => exact (Option.some.inj h).symm
  | cons tok ts ih =>
    cases hr : readToken code with
    | none => simp [matchTokens, hr] at h
    | some fields =>
      obtain ⟨hd, rest⟩ := fields
      by_cases eq : hd = tok
      · subst hd
        have hTail : matchTokens ts rest = some tail := by simpa [matchTokens, hr] using h
        simp only [encodeTokens, ih hTail]
        exact readToken_sound hr
      · simp [matchTokens, hr, eq] at h

theorem matchTokens_incumbent {ts : List Token} {tail : Nat} (xs : List Token)
    (h : matchTokens ts (encodeTokens xs 0) = some tail) :
    ∃ remaining, xs = ts ++ remaining ∧ tail = encodeTokens remaining 0 := by
  induction ts generalizing xs with
  | nil => exact ⟨xs, rfl, (Option.some.inj h).symm⟩
  | cons tok ts ih =>
    cases xs with
    | nil =>
      have empty : readToken 0 = none := rfl
      simp [encodeTokens, matchTokens, empty] at h
    | cons first xs =>
      have hr := readToken_encode first (encodeTokens xs 0)
      by_cases eq : first = tok
      · subst first
        have rest : matchTokens ts (encodeTokens xs 0) = some tail := by
          simpa [encodeTokens, matchTokens, hr] using h
        obtain ⟨remaining, shape, code⟩ := ih xs rest
        exact ⟨remaining, congrArg (List.cons tok) shape, code⟩
      · simp [encodeTokens, matchTokens, hr, eq] at h

theorem matchTokens_empty {b : Token} {ts : List Token} :
    matchTokens (b :: ts) 0 = none := by
  have empty : readToken 0 = none := rfl
  simp [matchTokens, empty]

end PalomarI3380
