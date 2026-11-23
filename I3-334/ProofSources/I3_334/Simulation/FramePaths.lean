module
public import I3_334.Simulation.DecoderWalk
@[expose] public section

namespace PalomarI3334.Decoder

open PalomarI3380
open Engine (breakPath incrementReversed stripThrough zeros)
open Control (root cut)

theorem ValidPrefix.initial (q : Nat) (front tail : List Bool)
    (h : ValidPrefix q (front ++ tail)) : ValidPrefix q front := by
  induction front generalizing q with
  | nil => trivial
  | cons b front ih => exact ⟨h.1, ih _ h.2⟩

theorem ValidPrefix.changeLast (q : Nat) (front : List Bool) (a b : Bool)
    (h : ValidPrefix q (front ++ [a])) : ValidPrefix q (front ++ [b]) := by
  induction front generalizing q with
  | nil => exact ⟨h.1, trivial⟩
  | cons bit front ih => exact ⟨h.1, ih _ h.2⟩

/-- A decoder frame consists of a valid initial instruction path
followed by zeros. Only an operation's temporary selection marks may
lie beyond the decoded instruction. -/
def Clean (path : List Bool) : Prop :=
  ∃ stem n, path = stem ++ zeros n ∧ ValidPrefix root stem

theorem clean_nil : Clean [] := ⟨[], 0, rfl, trivial⟩

private theorem appendZero {path : List Bool} (ready : Clean path) : Clean (path ++ [false]) := by
  obtain ⟨stem, n, rfl, valid⟩ := ready
  refine ⟨stem, n+1, ?_, valid⟩
  rw [List.append_assoc]
  congr 1
  change List.replicate n false ++ List.replicate 1 false = List.replicate (n+1) false
  rw [List.replicate_append_replicate]

theorem clean_increment (path : List Bool) (valid : ValidPrefix root path.reverse) :
    Clean (incrementReversed path).reverse := by
  induction path with
  | nil => exact clean_nil
  | cons bit path ih =>
    rw [List.reverse_cons] at valid
    cases bit
    · exact ⟨path.reverse ++ [true], 0, by simp [incrementReversed],
        ValidPrefix.changeLast root path.reverse false true valid⟩
    · have shorter := ValidPrefix.initial root path.reverse [true] valid
      simpa only [incrementReversed, List.reverse_cons] using appendZero (ih shorter)

private theorem strip_suffix (bit : Bool) (path : List Bool) :
    ∃ erased, path = erased ++ stripThrough bit path := by
  induction path with
  | nil => exact ⟨[], rfl⟩
  | cons first path ih =>
    by_cases eq : first = bit
    · exact ⟨[first], by simp [stripThrough, eq]⟩
    · obtain ⟨erased, same⟩ := ih
      exact ⟨first :: erased, by simpa only [stripThrough, eq, ↓reduceIte, List.cons_append,
        List.cons.injEq, true_and] using same⟩

theorem clean_break (path : List Bool) (skip : Bool) (valid : ValidPrefix root path.reverse) :
    Clean (breakPath skip path).reverse := by
  cases skip with
  | false => exact clean_increment path valid
  | true =>
    obtain ⟨erased, shape⟩ := strip_suffix false path
    have reversed := congrArg List.reverse shape
    rw [List.reverse_append] at reversed
    exact clean_increment _ (ValidPrefix.initial root _ erased.reverse (reversed ▸ valid))

theorem cut_suffix (path : List Bool) (skip : Nat) : ∃ erased, path = erased ++ cut path skip := by
  induction path generalizing skip with
  | nil => exact ⟨[], rfl⟩
  | cons bit path ih =>
    cases skip with
    | zero => cases bit <;> exact ⟨[], rfl⟩
    | succ n =>
      cases bit
      · obtain ⟨erased, eq⟩ := ih (n+1)
        exact ⟨false :: erased, congrArg (List.cons false) eq⟩
      · obtain ⟨erased, eq⟩ := ih n
        exact ⟨true :: erased, congrArg (List.cons true) eq⟩

theorem cut_zero (path : List Bool) : cut path 0 = path := by
  cases path <;> rfl

theorem clean_continue (path : List Bool) (skip : Nat) (valid : ValidPrefix root path.reverse) :
    Clean (cut path skip).reverse := by
  obtain ⟨erased, same⟩ := cut_suffix path skip
  have reversed := congrArg List.reverse same
  rw [List.reverse_append] at reversed
  exact ⟨(cut path skip).reverse, 0, by simp,
    ValidPrefix.initial root _ erased.reverse (reversed ▸ valid)⟩

theorem Decodes.rest_zeros {path : List Bool} {pad : Nat} {d : Result}
    (h : Decodes root [] (path ++ zeros pad) d) (clean : Clean path) :
    d.rest = zeros d.rest.length := by
  obtain ⟨stem, n, rfl, valid⟩ := clean
  have input : stem ++ zeros (n + pad) = (stem ++ zeros n) ++ zeros pad := by
    rw [List.append_assoc, List.replicate_append_replicate]
  have length := h.covers stem (zeros (n + pad)) valid input
  have suffix := congrArg (List.drop h.scanned.length) h.consumed
  have padded := congrArg (List.drop h.scanned.length) input
  rw [List.drop_append_length, ← padded, List.drop_append, List.drop_eq_nil_of_le length,
    List.nil_append, List.drop_replicate] at suffix
  have count := congrArg List.length suffix
  simp only [List.length_replicate] at count
  rw [count]
  exact suffix

theorem Decodes.before_valid {input : List Bool} {d : Result} (h : Decodes root [] input d) :
    ValidPrefix root d.before.reverse := by
  have scanned : h.scanned = d.path := h.path
  have valid : ValidPrefix root d.path := scanned ▸ h.invariant
  exact ValidPrefix.initial root d.before.reverse [d.read] valid

end PalomarI3334.Decoder
