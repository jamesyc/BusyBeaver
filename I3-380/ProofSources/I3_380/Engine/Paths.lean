module
public import I3_380.Engine.RegisterCycle
@[expose] public section

namespace PalomarI3380.Engine

/-- All a path's nonzero bits are contained in a valid decoder prefix. -/
def Clean (path : List Bool) : Prop :=
  ∃ stem zerosCount, path = stem ++ zeros zerosCount ∧ ValidPrefix Port.root stem

theorem clean_nil : Clean [] := ⟨[], 0, rfl, trivial⟩

theorem ValidPrefix.initial (q : Nat) (stem tail : List Bool)
    (h : ValidPrefix q (stem ++ tail)) : ValidPrefix q stem := by
  induction stem generalizing q with
  | nil => trivial
  | cons b rest ih =>
    simp only [List.cons_append, ValidPrefix] at h ⊢
    exact ⟨h.1, ih _ h.2⟩

theorem ValidPrefix.changeLast (q : Nat) (stem : List Bool) (a b : Bool)
    (h : ValidPrefix q (stem ++ [a])) : ValidPrefix q (stem ++ [b]) := by
  induction stem generalizing q with
  | nil => exact ⟨h.1, trivial⟩
  | cons bit rest ih =>
    simp only [List.cons_append, ValidPrefix] at h ⊢
    exact ⟨h.1, ih _ h.2⟩

private theorem increment_cases (path : List Bool) :
    (∃ n, path = ones n ∧ incrementReversed path = zeros n) ∨
    (∃ n front, path = ones n ++ false :: front ∧
      incrementReversed path = zeros n ++ true :: front) := by
  induction path with
  | nil => exact Or.inl ⟨0, rfl, rfl⟩
  | cons b rest ih =>
    cases b
    · exact Or.inr ⟨0, rest, rfl, rfl⟩
    · rcases ih with ⟨n, hPath, hInc⟩ | ⟨n, front, hPath, hInc⟩
      · exact Or.inl ⟨n + 1, congrArg (List.cons true) hPath, congrArg (List.cons false) hInc⟩
      · exact Or.inr ⟨n + 1, front, congrArg (List.cons true) hPath, congrArg (List.cons false) hInc⟩

theorem clean_increment (path : List Bool) (h : ValidPrefix Port.root path) :
    Clean (incrementReversed path.reverse).reverse := by
  rcases increment_cases path.reverse with ⟨n, _, heq⟩ | ⟨n, front, original, heq⟩
  · exact ⟨[], n, by rw [heq, reverse_zeros]; rfl, trivial⟩
  · have hReverse := congrArg List.reverse original
    simp only [List.reverse_reverse, List.reverse_append, reverse_ones, List.reverse_cons] at hReverse
    have hp : ValidPrefix Port.root (front.reverse ++ [false]) :=
      ValidPrefix.initial Port.root _ (ones n) (hReverse ▸ h)
    refine ⟨front.reverse ++ [true], n, ?_, ValidPrefix.changeLast Port.root front.reverse false true hp⟩
    rw [heq, List.reverse_append, reverse_zeros, List.reverse_cons]

private theorem strip_suffix (bit : Bool) (path : List Bool) :
    ∃ erased, path = erased ++ stripThrough bit path := by
  induction path with
  | nil => exact ⟨[], rfl⟩
  | cons front rest ih =>
    by_cases heq : front = bit
    · exact ⟨[front], by simp only [stripThrough, heq, ↓reduceIte, List.singleton_append]⟩
    · obtain ⟨erased, hErase⟩ := ih
      refine ⟨front :: erased, ?_⟩
      simp only [stripThrough, heq, ↓reduceIte, List.cons_append, List.cons.injEq, true_and]
      exact hErase

theorem valid_strip (bit : Bool) (backwards : List Bool)
    (h : ValidPrefix Port.root backwards.reverse) :
    ValidPrefix Port.root (stripThrough bit backwards).reverse := by
  obtain ⟨erased, hErase⟩ := strip_suffix bit backwards
  have hPath := congrArg List.reverse hErase
  rw [List.reverse_append] at hPath
  exact ValidPrefix.initial Port.root _ erased.reverse (hPath ▸ h)

theorem clean_break (backwards : List Bool) (skip : Bool)
    (h : ValidPrefix Port.root backwards.reverse) : Clean (breakPath skip backwards).reverse := by
  cases skip with
  | false =>
    simpa only [breakPath, Bool.false_eq_true, ↓reduceIte, List.reverse_reverse] using
      clean_increment backwards.reverse h
  | true =>
    simpa only [breakPath, ↓reduceIte, List.reverse_reverse] using
      clean_increment (stripThrough false backwards).reverse (valid_strip false backwards h)

theorem clean_continue (backwards : List Bool) (h : ValidPrefix Port.root backwards.reverse) :
    Clean (stripThrough true backwards).reverse :=
  ⟨(stripThrough true backwards).reverse, 0, (List.append_nil _).symm, valid_strip true backwards h⟩

theorem DecodedFrom.rest_zeros {path : List Bool} {gap : Nat} {d : Decoded}
    (h : DecodedFrom 59 Port.root [] (path ++ zeros gap) d.path d)
    (hClean : Clean path) : d.rest = zeros d.rest.length := by
  obtain ⟨stem, n, rfl, hStem⟩ := hClean
  have hInput : stem ++ zeros (n + gap) = (stem ++ zeros n) ++ zeros gap := by
    rw [List.append_assoc, List.replicate_append_replicate]
  have hLen := h.coversPrefix stem (zeros (n + gap)) hStem hInput
  have sep := congrArg (List.drop d.path.length) h.consumed
  rw [List.drop_append_length, ← hInput, List.drop_append, List.drop_eq_nil_of_le hLen,
    List.nil_append, List.drop_replicate] at sep
  have len := congrArg List.length sep
  simp only [List.length_replicate] at len
  rw [len]
  exact sep

theorem DecodedFrom.before_valid {input scanned : List Bool} {d : Decoded}
    (h : DecodedFrom 59 Port.root [] input scanned d) : ValidPrefix Port.root d.before.reverse := by
  have hp := h.validPrefix
  have heq : scanned = d.path := h.pathEq
  rw [heq, Decoded.path] at hp
  exact ValidPrefix.initial _ _ _ hp

end PalomarI3380.Engine
