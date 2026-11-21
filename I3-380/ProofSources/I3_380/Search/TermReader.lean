module
public import I3_380.Search.RawTerms
public import I3_380.Search.Cantor
@[expose] public section

namespace PalomarI3380

/-- Put token fields in front of an arbitrary remaining integer stream. -/
def encodeTokens : List Token → Nat → Nat
  | [], tail => tail
  | tok :: tokens, tail => Cantor.pair (tok.arity + 1)
      (Cantor.pair tok.tag (encodeTokens tokens tail))

theorem encodeTokens_append (xs ys : List Token) (tail : Nat) :
    encodeTokens (xs ++ ys) tail = encodeTokens xs (encodeTokens ys tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, encodeTokens, ih]

theorem encodeTokens_zero (xs : List Token) : encodeTokens xs 0 = wordCode xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [encodeTokens, wordCode, ih]

theorem encodeTokens_bound (xs : List Token) (tail : Nat) : tail + xs.length ≤ encodeTokens xs tail := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons tok xs ih =>
    have first := Cantor.right_lt_of_left_pos (a := tok.arity + 1) (by omega)
      (Cantor.pair tok.tag (encodeTokens xs tail))
    have second := Cantor.right_le tok.tag (encodeTokens xs tail)
    simp only [List.length_cons, encodeTokens]
    omega

def readToken (code : Nat) : Option (Token × Nat) :=
  let fields := Cantor.unpair code
  let tag := Cantor.unpair fields.2
  if fields.1 = 0 then none else some (⟨fields.1 - 1, tag.1⟩, tag.2)

theorem readToken_encode (tok : Token) (tail : Nat) :
    readToken (Cantor.pair (tok.arity + 1) (Cantor.pair tok.tag tail)) = some (tok, tail) := by
  rcases tok with ⟨arity, tag⟩
  simp only [readToken, Cantor.unpair_pair, Nat.succ_ne_zero, ↓reduceIte,
    Nat.add_sub_cancel_right]

theorem readToken_sound {code tail : Nat} {tok : Token}
    (h : readToken code = some (tok, tail)) :
    Cantor.pair (tok.arity + 1) (Cantor.pair tok.tag tail) = code := by
  simp only [readToken] at h
  split at h
  · contradiction
  · rename_i nonzero
    cases h
    simp only
    have hPos : (Cantor.unpair code).1 - 1 + 1 = (Cantor.unpair code).1 := by omega
    rw [hPos, Cantor.pair_unpair, Cantor.pair_unpair]

/-- A parser for a sequence of complete terms. It processes only the first
complete terms and leaves the remaining word intact. -/
def parseForest : Nat → Nat → Nat → Option (List RawTerm × Nat)
  | _, 0, code => some ([], code)
  | 0, _ + 1, _ => none
  | fuel + 1, count + 1, code => do
    let (tok, body) ← readToken code
    let (children, suffix) ← parseForest fuel tok.arity body
    let (siblings, tail) ← parseForest fuel count suffix
    return (RawTerm.app tok.tag children :: siblings, tail)

theorem parseForest_sound {fuel count code : Nat} {ts : List RawTerm} {tail : Nat}
    (h : parseForest fuel count code = some (ts, tail)) :
    ts.length = count ∧ encodeTokens (ts.flatMap RawTerm.tokens) tail = code := by
  induction fuel generalizing count code ts tail with
  | zero =>
    cases count with
    | zero =>
      simp [parseForest] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    | succ count => simp [parseForest] at h
  | succ fuel ih =>
    cases count with
    | zero =>
      simp [parseForest] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    | succ count =>
      cases hr : readToken code with
      | none => simp [parseForest, hr] at h
      | some read =>
        rcases read with ⟨tok, body⟩
        cases hChildren : parseForest fuel tok.arity body with
        | none => simp [parseForest, hr, hChildren] at h
        | some subtree =>
          rcases subtree with ⟨children, suffix⟩
          cases hSiblings : parseForest fuel count suffix with
          | none => simp [parseForest, hr, hChildren, hSiblings] at h
          | some siblings =>
            rcases siblings with ⟨siblings, remaining⟩
            simp [parseForest, hr, hChildren, hSiblings] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hc, hBody⟩ := ih hChildren
            obtain ⟨hs, hSuffix⟩ := ih hSiblings
            constructor
            · simp only [List.length_cons, hs]
            · simp only [List.flatMap_cons, RawTerm.tokens_app, List.cons_append, encodeTokens,
                encodeTokens_append, hSuffix, hBody, hc]
              exact readToken_sound hr

theorem parseForest_complete (fuel : Nat) (ts : List RawTerm) (tail : Nat)
    (bound : (ts.flatMap RawTerm.tokens).length ≤ fuel) :
    parseForest fuel ts.length (encodeTokens (ts.flatMap RawTerm.tokens) tail) = some (ts, tail) := by
  induction fuel generalizing ts tail with
  | zero =>
    cases ts with
    | nil => rfl
    | cons t ts =>
      cases t with
      | app tag children =>
        simp only [List.flatMap_cons, RawTerm.tokens_app, List.cons_append, List.length_cons] at bound
        omega
  | succ fuel ih =>
    cases ts with
    | nil => rfl
    | cons t siblings =>
      cases t with
      | app tag children =>
        simp only [List.flatMap_cons, RawTerm.tokens_app, List.cons_append, List.length_cons,
          List.length_append] at bound
        have hChildren := ih children (encodeTokens (siblings.flatMap RawTerm.tokens) tail) (by omega)
        have hSiblings := ih siblings tail (by omega)
        let rest := encodeTokens (siblings.flatMap RawTerm.tokens) tail
        let body := encodeTokens (children.flatMap RawTerm.tokens) rest
        have read : readToken (Cantor.pair (children.length + 1) (Cantor.pair tag body)) =
            some (⟨children.length, tag⟩, body) := readToken_encode ⟨children.length, tag⟩ body
        simp only [List.length_cons, List.flatMap_cons, RawTerm.tokens_app, List.cons_append,
          encodeTokens, encodeTokens_append, parseForest, show
            readToken (Cantor.pair (children.length + 1) (Cantor.pair tag
              (encodeTokens (children.flatMap RawTerm.tokens)
                (encodeTokens (siblings.flatMap RawTerm.tokens) tail)))) =
              some (⟨children.length, tag⟩, body) from read]
        simp [body, rest, hChildren, hSiblings]

def readTree (code : Nat) : Option (RawTerm × Nat) :=
  match parseForest code 1 code with
  | some ([t], rest) => some (t, rest)
  | _ => none

theorem readTree_complete (t : RawTerm) (remaining : Nat) :
    readTree (encodeTokens t.tokens remaining) = some (t, remaining) := by
  have b := encodeTokens_bound t.tokens remaining
  have h := parseForest_complete (encodeTokens t.tokens remaining) [t] remaining (by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega)
  simp only [List.length_cons, List.length_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
  simp only [readTree, h]

theorem readTree_sound {code remaining : Nat} {t : RawTerm}
    (h : readTree code = some (t, remaining)) :
    encodeTokens t.tokens remaining = code := by
  unfold readTree at h
  cases hp : parseForest code 1 code with
  | none => simp [hp] at h
  | some parsed =>
    obtain ⟨trees, rest⟩ := parsed
    cases trees with
    | nil => simp [hp] at h
    | cons tree siblings =>
      cases siblings with
      | cons other others => simp [hp] at h
      | nil =>
        simp [hp] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using (parseForest_sound hp).2

theorem RawTerm.prefix_unique {x y : RawTerm} {xs ys : List Token}
    (eq : x.tokens ++ xs = y.tokens ++ ys) : x = y ∧ xs = ys := by
  have hCode := congrArg (fun word => encodeTokens word 0) eq
  simp only [encodeTokens_append] at hCode
  have hRead := congrArg readTree hCode
  simp only [readTree_complete, Option.some.injEq, Prod.mk.injEq, encodeTokens_zero] at hRead
  exact ⟨hRead.1, wordCode_injective hRead.2⟩

end PalomarI3380
