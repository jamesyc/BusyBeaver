module
public import I0451.Issue
public import I0451.RegisterDecrement

/-! Complete register access from a decoder frame with sufficient gap.
A finite number of selector passes places the extra separator before
the desired register. Each pass is proved for the literal machine. -/
@[expose] public section
namespace I0451.Runtime

/-- A clean configuration at the root of the decoder. -/
def frame (word : List Bool) (gap : Nat) (regs : List Nat) : Config :=
  ⟨root, 1, pack word (pack (List.replicate gap false) (pack (blocks regs) 0))⟩

private def intermediate (word : List Bool) (m gap : Nat) (before after : List Nat) : Config :=
  ⟨root, 1, pack (word ++ List.replicate m true)
    (pack (List.replicate gap false ++ blocks before) (push false (pack (blocks after) 0)))⟩

private theorem select_many (op : RegisterOp) {i : Nat} {word : List Bool}
    (bounded : i < 9) (path : Decoder.IssuePath root true false word (op.issue i))
    (safe : SafeDispatch 0 word.reverse) (gap x : Nat) (xs : List Nat)
    (todo selected : List Nat) (m : Nat) (within : m + todo.length ≤ i + 1) :
    Reaches literal (intermediate word m (gap + todo.length + 3)
      (x :: xs ++ todo.reverse) selected)
      (intermediate word (m + todo.length) (gap + 3)
        (x :: xs) (todo.reverse ++ selected)) := by
  induction todo generalizing selected m with
  | nil => exact ⟨0, by simp [run]⟩
  | cons x' todo ih =>
    have available : m ≤ i := by simp only [List.length_cons] at within; omega
    have first := select_pass op bounded available path safe (gap + todo.length) x
      (xs ++ todo.reverse) x' (pack (blocks selected) 0)
    have selectedTape : pack (blocks [x']) (pack (blocks selected) 0) =
        pack (blocks (x' :: selected)) 0 := by
      rw [← pack_append, ← blocks_append]
      rfl
    rw [selectedTape] at first
    have firstStage : Reaches literal
        (intermediate word m (gap + todo.length + 4)
          (x :: (xs ++ todo.reverse) ++ [x']) selected)
        (intermediate word (m + 1) (gap + todo.length + 3)
          (x :: xs ++ todo.reverse) (x' :: selected)) := first
    have tail := ih (x' :: selected) (m + 1) (by simp only [List.length_cons] at within; omega)
    have lengthEq : gap + (todo.length + 1) + 3 = gap + todo.length + 4 := by omega
    have flagsEq : m + (todo.length + 1) = (m + 1) + todo.length := by omega
    simpa only [List.reverse_cons, List.append_assoc, List.length_cons, lengthEq,
      flagsEq, List.singleton_append, List.cons_append, List.nil_append] using firstStage.trans tail

/-- Enter an operation with the intended register under the selector.
The previously unselected blocks form a nonempty prefix. -/
theorem reach_selected (op : RegisterOp) {i : Nat} {word : List Bool}
    (bounded : i < 9) (path : Decoder.IssuePath root true false word (op.issue i))
    (safe : SafeDispatch 0 word.reverse) (gap x value : Nat)
    (xs suffix : List Nat) (index : suffix.length = i) :
    Reaches literal
      (frame word (gap + (i + 1) + 3) (x :: xs ++ value :: suffix))
      ⟨op.entry, pack (word ++ List.replicate (i + 1) true).reverse 1,
        push false (pack (List.replicate (gap + 2) false ++ blocks (x :: xs))
          (push false (pack (blocks (value :: suffix)) 0)))⟩ := by
  have length : (value :: suffix).reverse.length = i + 1 := by simp [index]
  have moved := select_many op bounded path safe gap x xs (value :: suffix).reverse [] 0
    (by rw [length, Nat.zero_add]; exact Nat.le_refl _)
  simp only [length, Nat.zero_add, List.reverse_reverse, List.append_nil] at moved
  have finiteTape : push false (pack (blocks []) 0) = 0 := rfl
  have start : intermediate word 0 (gap + (i + 1) + 3) (x :: xs ++ value :: suffix) [] =
      frame word (gap + (i + 1) + 3) (x :: xs ++ value :: suffix) := by
    simp [intermediate, frame, pack_append, finiteTape]
  rw [start] at moved
  have tail : pack (List.replicate (gap + 3) false ++ blocks (x :: xs))
      (push false (pack (blocks (value :: suffix)) 0)) =
      push false (pack (List.replicate (gap + 2) false ++ blocks (x :: xs))
        (push false (pack (blocks (value :: suffix)) 0))) := by
    rw [show gap + 3 = (gap + 2) + 1 by omega, List.replicate_succ, List.cons_append, pack_cons]
  simp only [intermediate, tail] at moved
  exact moved.trans (enter op bounded path _)

private theorem carry_flags (n : Nat) (rev : List Bool) :
    carry (List.replicate n true ++ rev) = List.replicate n false ++ carry rev := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, carry] using congrArg (false :: ·) ih

private theorem return_after_flags {word : List Bool} (safe : SafeDispatch 0 word.reverse)
    (flags gap : Nat) (regs : List Nat) :
    Reaches literal
      (fromLeft breakZero (pack (word ++ List.replicate flags true).reverse 1)
        (pack (List.replicate gap false) (pack (blocks regs) 0)))
      (frame (carry word.reverse).reverse (flags + gap) regs) := by
  have safeFlags : SafeDispatch 0 (word ++ List.replicate flags true).reverse := by
    simpa [List.reverse_append] using safe.ones flags
  have back := break_zero safeFlags (pack (List.replicate gap false) (pack (blocks regs) 0))
  simpa [frame, List.reverse_append, carry_flags, pack_append, pack_repeats] using back

/-- An increment instruction at a sufficiently padded decoder frame.
All selection flags are removed before returning to the next frame. -/
theorem increment_register {i : Nat} {word : List Bool}
    (bounded : i < 9) (path : Decoder.IssuePath root true false word (RegisterOp.inc.issue i))
    (safe : SafeDispatch 0 word.reverse) (gap x value : Nat)
    (xs suffix : List Nat) (index : suffix.length = i) :
    Advances literal
      (frame word (gap + (i + 1) + 3) (x :: xs ++ value :: suffix))
      (frame (carry word.reverse).reverse (gap + (i + 1) + 3)
        (x :: xs ++ (value + 1) :: suffix)) := by
  let flags := word ++ List.replicate (i + 1) true
  have selected := reach_selected .inc bounded path safe gap x value xs suffix index
  have positive := increment_selected gap x xs (pack flags.reverse 1)
    (pack (blocks (value :: suffix)) 0)
  have newValue : push true (pack (blocks (value :: suffix)) 0) =
      pack (blocks ((value + 1) :: suffix)) 0 := by
    simp [blocks, List.replicate_succ, pack_append]
  rw [newValue] at positive
  have updateTape : pack (List.replicate (gap + 3) false ++ blocks (x :: xs))
      (pack (blocks ((value + 1) :: suffix)) 0) =
      pack (List.replicate (gap + 3) false)
        (pack (blocks (x :: xs ++ (value + 1) :: suffix)) 0) := by
    rw [pack_append]
    have join := pack_append (blocks (x :: xs)) (blocks ((value + 1) :: suffix)) 0
    rw [← blocks_append] at join
    exact congrArg (pack (List.replicate (gap + 3) false)) join.symm
  rw [updateTape] at positive
  have back := return_after_flags safe (i + 1) (gap + 3) (x :: xs ++ (value + 1) :: suffix)
  have gapEq : (i + 1) + (gap + 3) = gap + (i + 1) + 3 := by omega
  rw [gapEq] at back
  exact (selected.positive_of_state_ne (by change root ≠ increment; decide +kernel)).trans (positive.trans back)

/-- A nonzero decrement reduces the register and increases the gap. -/
theorem decrement_register_pos {i : Nat} {word : List Bool}
    (bounded : i < 9) (path : Decoder.IssuePath root true false word (RegisterOp.dec.issue i))
    (safe : SafeDispatch 0 word.reverse) (gap x value : Nat)
    (xs suffix : List Nat) (index : suffix.length = i) :
    Advances literal
      (frame word (gap + (i + 1) + 3) (x :: xs ++ (value + 1) :: suffix))
      (frame (carry word.reverse).reverse (gap + (i + 1) + 4)
        (x :: xs ++ value :: suffix)) := by
  let flags := word ++ List.replicate (i + 1) true
  have selected := reach_selected .dec bounded path safe gap x (value + 1) xs suffix index
  have positive := decrement_positive gap x value xs suffix (pack flags.reverse 1)
  simp only [pack_append] at selected positive
  have back := return_after_flags safe (i + 1) (gap + 4) (x :: xs ++ value :: suffix)
  have gapEq : (i + 1) + (gap + 4) = gap + (i + 1) + 4 := by omega
  rw [gapEq] at back
  exact (selected.positive_of_state_ne (by change root ≠ decrement; decide +kernel)).trans (positive.trans back)

/-- A zero decrement takes the failure return and leaves every register
unchanged. The first available zero in the address is the jump delimiter. -/
theorem decrement_register_zero {i : Nat} {word rev : List Bool}
    (bounded : i < 9) (path : Decoder.IssuePath root true false word (RegisterOp.dec.issue i))
    (safe : SafeDispatch 0 word.reverse) (restSafe : SafeDispatch 0 rev)
    (gap last trailing : Nat) (before suffix : List Nat) (index : suffix.length = i)
    (split : word.reverse = List.replicate trailing true ++ false :: rev) :
    Advances literal
      (frame word (gap + (i + 1) + 3) (before ++ last :: 0 :: suffix))
      (frame (carry rev).reverse (gap + (i + 1) + 4 + trailing + 1)
        (before ++ last :: 0 :: suffix)) := by
  let flags := word ++ List.replicate (i + 1) true
  let regs := before ++ last :: 0 :: suffix
  have ready : Reaches literal (frame word (gap + (i + 1) + 3) regs)
      ⟨decrement, pack flags.reverse 1,
        push false (pack (List.replicate (gap + 2) false ++ blocks (before ++ [last]))
          (push false (pack (blocks (0 :: suffix)) 0)))⟩ := by
    cases before with
    | nil => exact reach_selected .dec bounded path safe gap last 0 [] suffix index
    | cons b bs =>
      simpa only [regs, flags, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append, RegisterOp.entry]
        using reach_selected .dec bounded path safe gap b 0 (bs ++ [last]) suffix index
  have check := decrement_zero gap last before suffix (pack flags.reverse 1)
  simp only [pack_append] at ready check
  have reverseFlags : flags.reverse = List.replicate ((i + 1) + trailing) true ++ false :: rev := by
    simp [flags, List.reverse_append, split, ← List.append_assoc]
  rw [reverseFlags, pack_append, pack_cons] at ready check
  have back := break_one restSafe ((i + 1) + trailing)
    (pack (List.replicate (gap + 4) false) (pack (blocks regs) 0))
  have adjusted : push false (pack (List.replicate ((i + 1) + trailing) false)
      (pack (List.replicate (gap + 4) false) (pack (blocks regs) 0))) =
    pack (List.replicate (gap + (i + 1) + 4 + trailing + 1) false) (pack (blocks regs) 0) := by
    rw [pack_repeats, ← pack_cons, ← List.replicate_succ]
    congr 2
    omega
  rw [adjusted] at back
  exact (ready.positive_of_state_ne (by change root ≠ decrement; decide +kernel)).trans (check.trans back)

end I0451.Runtime
