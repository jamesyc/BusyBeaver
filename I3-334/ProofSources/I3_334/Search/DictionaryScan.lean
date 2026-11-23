module
public import I3_334.Search.Dictionary
public import I3_334.Search.Templates
@[expose] public section

namespace PalomarI3334

open PalomarI3380

/-- The unbiased reader's arity and remaining word fit within the input
word. This includes the zero word, which supplies a nullary default. -/
theorem readRaw_budget (offset word : Nat) :
    (readRaw offset word).1.arity + (readRaw offset word).2 ≤ word := by
  have pair_budget (a b : Nat) : a + b ≤ Cantor.pair a b := by
    rw [Cantor.pair_as_triangle, ← Cantor.diagonalStart_eq]
    have := Cantor.diagonalStart_lower (a + b)
    omega
  rcases h : Cantor.unpair word with ⟨arity, body⟩
  rcases hb : Cantor.unpair body with ⟨tag, tail⟩
  have first := Cantor.pair_unpair word
  have second := Cantor.pair_unpair body
  rw [h] at first
  rw [hb] at second
  simp only [readRaw, h, hb]
  have ba := pair_budget arity body
  have bt := pair_budget tag tail
  rw [first] at ba
  rw [second] at bt
  omega

/-- Emit the tokens of a fixed number of raw terms and return the
unused word. A zero word still consumes one nullary default per slot. -/
def scanRaw (offset : Nat) (word : Nat) : (pending : Nat) → List Token × Nat
  | 0 => ([], word)
  | pending + 1 =>
    let next := readRaw offset word
    let result := scanRaw offset next.2 (pending + next.1.arity)
    (next.1 :: result.1, result.2)
termination_by pending => word + pending
decreasing_by
  have h := readRaw_budget offset word
  simp_wf
  omega

theorem writeRaw_append (offset : Nat) (xs ys : List Token) (tail : Nat) :
    writeRaw offset (xs ++ ys) tail = writeRaw offset xs (writeRaw offset ys tail) := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.cons_append, writeRaw, ih]

theorem scanRaw_cons (offset : Nat) (word : Nat) (pending : Nat) :
    scanRaw offset word (pending + 1) =
      ((readRaw offset word).1 ::
        (scanRaw offset (readRaw offset word).2 (pending + (readRaw offset word).1.arity)).1,
        (scanRaw offset (readRaw offset word).2 (pending + (readRaw offset word).1.arity)).2) := by
  rw [scanRaw]

theorem scanRaw_concat (offset : Nat) (word : Nat) (a b : Nat) :
    scanRaw offset word (b + a) =
      let first := scanRaw offset word a
      let second := scanRaw offset first.2 b
      (first.1 ++ second.1, second.2) := by
  induction h : word + a using Nat.strongRecOn generalizing word a with
  | ind n ih =>
    cases a with
    | zero => simp [scanRaw]
    | succ a =>
      let next := readRaw offset word
      have smaller : next.2 + (a + next.1.arity) < n := by
        have bound := readRaw_budget offset word
        change (readRaw offset word).1.arity + (readRaw offset word).2 ≤ word at bound
        dsimp only [next]
        omega
      have add : b + a + next.1.arity = b + (a + next.1.arity) := Nat.add_assoc _ _ _
      have first := ih _ smaller next.2 (a + next.1.arity) rfl
      change scanRaw offset word (b + a + 1) = _
      rw [scanRaw_cons, scanRaw_cons offset word a]
      change (next.1 :: (scanRaw offset next.2 (b + a + next.1.arity)).1,
          (scanRaw offset next.2 (b + a + next.1.arity)).2) = _
      rw [add, first]
      rfl

theorem scanRaw_sound (offset word pending : Nat) :
    ∃ trees : List RawTerm, trees.length = pending ∧
      trees.flatMap RawTerm.tokens = (scanRaw offset word pending).1 ∧
      ∀ tok ∈ trees.flatMap RawTerm.tokens, offset ≤ tok.tag := by
  induction size : word + pending using Nat.strongRecOn generalizing word pending with
  | ind measure ih =>
    cases pending with
    | zero => exact ⟨[], rfl, by rw [scanRaw]; rfl, by simp⟩
    | succ count =>
      let next := readRaw offset word
      have smaller : next.2 + (count + next.1.arity) < measure := by
        have bound := readRaw_budget offset word
        dsimp only [next]
        omega
      obtain ⟨forest, len, decoded, allowed⟩ := ih _ smaller next.2 (count + next.1.arity) rfl
      let children := forest.take next.1.arity
      let siblings := forest.drop next.1.arity
      have childLen : children.length = next.1.arity := by
        simp only [children, List.length_take, len]
        omega
      have siblingLen : siblings.length = count := by
        simp only [siblings, List.length_drop, len]
        omega
      have tokens :
          ((RawTerm.app next.1.tag children :: siblings).flatMap RawTerm.tokens) =
            ⟨next.1.arity, next.1.tag⟩ :: forest.flatMap RawTerm.tokens := by
        simp only [List.flatMap_cons, RawTerm.tokens_app, List.cons_append, childLen]
        rw [← List.flatMap_append, List.take_append_drop]
      refine ⟨.app next.1.tag children :: siblings, by simp only [List.length_cons, siblingLen], ?_, ?_⟩
      · rw [tokens, decoded, scanRaw_cons]
      · intro tok mem
        rw [tokens, List.mem_cons] at mem
        rcases mem with rfl | mem
        · unfold next readRaw
          split
          split
          exact Nat.le_add_left _ _
        · exact allowed _ mem

theorem scanRaw_writeRaw (offset : Nat) : (trees : List RawTerm) → (tail : Nat) →
    (∀ tok ∈ trees.flatMap RawTerm.tokens, offset ≤ tok.tag) →
    scanRaw offset (writeRaw offset (trees.flatMap RawTerm.tokens) tail) trees.length =
      (trees.flatMap RawTerm.tokens, tail)
  | [], tail, _ => by simp [scanRaw, writeRaw]
  | .app tag children :: rest, tail, allowed => by
    simp only [List.flatMap_cons, RawTerm.tokens_app, List.cons_append, List.length_cons] at allowed ⊢
    have tagBound := allowed ⟨children.length, tag⟩ List.mem_cons_self
    have remaining (t : Token) (mem : t ∈ children.flatMap RawTerm.tokens ++ rest.flatMap RawTerm.tokens) :
        offset ≤ t.tag := allowed t (List.mem_cons_of_mem _ mem)
    let mid := writeRaw offset (rest.flatMap RawTerm.tokens) tail
    let childCode := writeRaw offset (children.flatMap RawTerm.tokens) mid
    have read :
        readRaw offset (Cantor.pair children.length (Cantor.pair (tag - offset) childCode)) =
          (⟨children.length, tag⟩, childCode) := by
      have n : offset ≤ tag := tagBound
      simp [readRaw, Cantor.unpair_pair, Nat.sub_add_cancel n]
    rw [writeRaw, writeRaw_append, scanRaw_cons]
    change ( (readRaw offset (Cantor.pair children.length
        (Cantor.pair (tag - offset) childCode))).1 :: _, _) = _
    rw [read]
    simp only
    rw [scanRaw_concat]
    have child := scanRaw_writeRaw offset children mid
      (fun t ht => remaining t (List.mem_append_left _ ht))
    have siblings := scanRaw_writeRaw offset rest tail
      (fun t ht => remaining t (List.mem_append_right _ ht))
    change (⟨children.length, tag⟩ :: ((scanRaw offset childCode children.length).1 ++
        (scanRaw offset (scanRaw offset childCode children.length).2 rest.length).1),
        (scanRaw offset (scanRaw offset childCode children.length).2 rest.length).2) = _
    rw [child]
    simpa only using congrArg (fun p : List Token × Nat =>
      (⟨children.length, tag⟩ :: (children.flatMap RawTerm.tokens ++ p.1), p.2)) siblings
termination_by trees _ _ => sizeOf trees
decreasing_by all_goals simp_wf; omega

end PalomarI3334
