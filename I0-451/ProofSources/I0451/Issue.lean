module
public import I0451.Decoder
public import I0451.RegisterSelect

/-! Register issue and selection. The selector returns to the same
instruction with one extra one after the consumed decoder word. -/
@[expose] public section
namespace I0451.Runtime

inductive RegisterOp where
  | inc
  | dec

def RegisterOp.entry : RegisterOp → Nat
  | .inc => increment
  | .dec => decrement

/-- Issue controls from the nearest register to the farthest. -/
def RegisterOp.issue (op : RegisterOp) (n : Nat) : Nat :=
  (match op with | .inc => incStates | .dec => decStates)[n]?.getD op.entry

namespace IssueRows

theorem issueZeroRow (op : RegisterOp) :
    row literal (op.issue 0) true = transition true true op.entry := by
  cases op <;> decide +kernel

theorem issueTrue (op : RegisterOp) {i : Nat} (h : i + 1 < 9) :
    row literal (op.issue (i + 1)) true = transition true true (op.issue i) := by
  have checked : (List.range 8).all (fun j =>
      row literal (op.issue (j + 1)) true == transition true true (op.issue j)) = true := by
    cases op <;> decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp checked i (List.mem_range.mpr (by omega)))

theorem issueFalse (op : RegisterOp) {i : Nat} (h : i < 9) :
    row literal (op.issue i) false = transition false true select := by
  have checked : (List.range 9).all (fun j =>
      row literal (op.issue j) false == transition false true select) = true := by
    cases op <;> decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp checked i (List.mem_range.mpr h))

end IssueRows

open IssueRows

private theorem countOnes (op : RegisterOp) {i m : Nat} (bounded : i < 9) (available : m ≤ i) (l r : Nat) :
    Reaches literal ⟨op.issue i, l, pack (List.replicate m true) r⟩
      ⟨op.issue (i - m), pack (List.replicate m true) l, r⟩ := by
  induction m generalizing i l with
  | zero => exact ⟨0, rfl⟩
  | succ m ih =>
    cases i with
    | zero => omega
    | succ i =>
      rw [pack_repeat_last true m l, List.replicate_succ, pack_cons]
      have arithmetic : i + 1 - (m + 1) = i - m := by omega
      rw [arithmetic]
      exact (Reaches.right (issueTrue op bounded) l _).trans
        (ih (by omega) (by omega) (push true l))

/-- The first phase of the register access, through the word and its
existing selector flags. -/
theorem issued (op : RegisterOp) {i m : Nat} {word : List Bool} (bounded : i < 9) (available : m ≤ i)
    (path : Decoder.IssuePath root true false word (op.issue i)) (r : Nat) :
    Reaches literal ⟨root, 1, pack (word ++ List.replicate m true) r⟩
      ⟨op.issue (i - m), pack (word ++ List.replicate m true).reverse 1, r⟩ := by
  simp only [List.reverse_append, List.reverse_replicate, pack_append]
  exact (path.read_root _).trans (countOnes op bounded available _ _)

/-- Move one register across the selector boundary, adding a flag to the
instruction word and consuming one zero of gap. -/
theorem select_pass (op : RegisterOp) {i m : Nat} {word : List Bool}
    (bounded : i < 9) (available : m ≤ i)
    (path : Decoder.IssuePath root true false word (op.issue i))
    (safe : SafeDispatch 0 word.reverse) (gap x : Nat) (xs : List Nat) (u r : Nat) :
    Reaches literal
      ⟨root, 1, pack (word ++ List.replicate m true)
        (pack (List.replicate (gap + 4) false ++ blocks (x :: xs ++ [u])) (push false r))⟩
      ⟨root, 1, pack (word ++ List.replicate (m + 1) true)
        (pack (List.replicate (gap + 3) false ++ blocks (x :: xs))
          (push false (pack (blocks [u]) r)))⟩ := by
  let flags := word ++ List.replicate m true
  let tail := pack (List.replicate (gap + 2) false ++ blocks (x :: xs ++ [u])) (push false r)
  let changed := pack (List.replicate (gap + 3) false ++ blocks (x :: xs))
        (push false (pack (blocks [u]) r))
  have zeros : pack (List.replicate (gap + 4) false ++ blocks (x :: xs ++ [u])) (push false r)
      = push false (push false tail) := by
    rw [show gap + 4 = (gap + 2 + 1) + 1 by omega]
    simp [List.replicate_succ, tail]
  rw [zeros]
  have issue := issued op bounded available path (push false (push false tail))
  have enter := Reaches.right (issueFalse op (i := i - m) (by omega)) (pack flags.reverse 1)
    (push false tail)
  have shift := select_preceding gap x xs u (push false (pack flags.reverse 1)) r
  have safeFlags : SafeDispatch 0 flags.reverse := by
    simpa [flags, List.reverse_append] using safe.ones m
  have back : Reaches literal (fromLeft breakZero (push false (pack flags.reverse 1)) changed)
      ⟨root, 1, pack (word ++ List.replicate (m + 1) true) changed⟩ := by
    rw [List.replicate_succ', ← List.append_assoc]
    exact advance_address safeFlags 0 changed
  exact issue.trans (enter.trans (shift.trans back))

/-- Once all flags are set, control enters the selected register operation. -/
theorem enter (op : RegisterOp) {i : Nat} {word : List Bool} (bounded : i < 9)
    (path : Decoder.IssuePath root true false word (op.issue i)) (r : Nat) :
    Reaches literal ⟨root, 1, pack (word ++ List.replicate (i + 1) true) r⟩
      ⟨op.entry, pack (word ++ List.replicate (i + 1) true).reverse 1, r⟩ := by
  rw [List.replicate_succ', ← List.append_assoc, pack_append, List.reverse_append, pack_append]
  have stage := issued op bounded (Nat.le_refl i) path (push true r)
  rw [Nat.sub_self] at stage
  simpa only [pack_append, List.reverse_singleton, pack_cons, pack_nil] using
    stage.trans (Reaches.right (issueZeroRow op) _ r)

end I0451.Runtime
