module
public import I0451.TapeRuns
public import I0451.Tables

/-! Increment from an established double-zero selector. Both the outward
and return scans are verified from the literal rows, for arbitrary unary
block lengths. -/

@[expose] public section
namespace I0451.Runtime

/-- A register block is its unary word followed by a zero separator. -/
def blocks : List Nat → List Bool
  | [] => []
  | n :: ns => List.replicate (n + 1) true ++ false :: blocks ns

theorem blocks_append (as bs : List Nat) : blocks (as ++ bs) = blocks as ++ blocks bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [blocks, ih, List.append_assoc]

private def remainder (n : Nat) (ns : List Nat) : List Bool :=
  List.replicate n true ++ false :: blocks ns

namespace IncrementRows

theorem gapZero : row literal incrementGap false = transition false true incrementGap := by decide +kernel
theorem gapOne : row literal incrementGap true = transition true true incrementOnes := by decide +kernel
theorem onesOne : row literal incrementOnes true = transition true true incrementOnes := by decide +kernel
theorem onesZero : row literal incrementOnes false = transition false true incrementSeparator := by decide +kernel
theorem sepOne : row literal incrementSeparator true = transition true true incrementOnes := by decide +kernel
theorem sepZero : row literal incrementSeparator false = transition true false returnStart := by decide +kernel
theorem entryZero : row literal increment false = transition true true incrementGap := by decide +kernel

end IncrementRows

open IncrementRows

private theorem nextBlock (n k : Nat) (ks : List Nat) :
    remainder n (k :: ks) = (List.replicate n true ++ [false, true]) ++ remainder k ks := by
  simp [remainder, blocks, List.replicate_succ, List.append_assoc]

private theorem overOnes (n l r : Nat) :
    Reaches literal
      ⟨incrementOnes, l, pack (List.replicate n true) (push false r)⟩
      ⟨incrementSeparator, push false (pack (List.replicate n true) l), r⟩ :=
  (show Reaches literal _ _ from ⟨n, scan_right onesOne n l (push false r)⟩).trans
    (Reaches.right onesZero _ _)

private theorem incrementRemainder (n : Nat) (ns : List Nat) (l r : Nat) :
    Reaches literal
      ⟨incrementOnes, l, pack (remainder n ns) (push false r)⟩
      (fromLeft returnStart (pack (remainder n ns).reverse l) (push true r)) := by
  induction ns generalizing n l with
  | nil =>
    have run := (overOnes n l (push false r)).trans (Reaches.left sepZero false _ _)
    simpa [remainder, blocks, List.reverse_append, pack_append] using run
  | cons k ks ih =>
    have entered := overOnes n l (push true (pack (remainder k ks) (push false r)))
    have run := entered.trans ((Reaches.right sepOne _ _).trans (ih k _))
    simpa [nextBlock, List.reverse_append, pack_append] using run

/-- From the zero following the instruction pointer, increment writes a
return marker, crosses the gap and register prefix, and sets the second
selector cell to one. -/
theorem increment_forward (gap n : Nat) (ns : List Nat) (l r : Nat) :
    Reaches literal
      ⟨increment, l, push false (pack (List.replicate gap false ++ blocks (n :: ns))
        (push false r))⟩
      (fromLeft returnStart
        (pack (blocks (n :: ns)).reverse (pack (List.replicate gap false) (push true l)))
        (push true r)) := by
  rw [pack_append]
  let gapLeft := pack (List.replicate gap false) (push true l)
  have blockStart : blocks (n :: ns) = true :: remainder n ns := by
    simp [blocks, remainder, List.replicate_succ]
  rw [blockStart]
  simp only [pack_cons, List.reverse_cons, pack_append, pack_nil]
  have first := Reaches.right entryZero l
    (pack (List.replicate gap false) (push true (pack (remainder n ns) (push false r))))
  have cross : Reaches literal _ _ :=
    ⟨gap, scan_right gapZero gap (push true l) (push true (pack (remainder n ns) (push false r)))⟩
  exact first.trans (cross.trans ((Reaches.right gapOne gapLeft _).trans
    (incrementRemainder n ns (push true gapLeft) r)))

inductive ReturnMode where
  | success
  | failure

def ReturnMode.entry : ReturnMode → Nat
  | .success => returnStart
  | .failure => returnFail

def ReturnMode.afterZero : ReturnMode → Nat
  | .success => returnOneZero
  | .failure => returnFailOneZero

def ReturnMode.gap : ReturnMode → Nat
  | .success => returnGap
  | .failure => returnFailGap

def ReturnMode.finish : ReturnMode → Nat
  | .success => breakZero
  | .failure => breakOne

namespace ReturnRows

theorem retOne (mode : ReturnMode) : row literal mode.entry true = transition true false mode.entry := by cases mode <;> decide +kernel
theorem retZero (mode : ReturnMode) : row literal mode.entry false = transition false false mode.afterZero := by cases mode <;> decide +kernel
theorem retOneZeroOne (mode : ReturnMode) :
    row literal mode.afterZero true = transition true false mode.entry := by cases mode <;> decide +kernel
theorem retOneZeroZero (mode : ReturnMode) :
    row literal mode.afterZero false = transition false false mode.gap := by cases mode <;> decide +kernel
theorem retGapZero (mode : ReturnMode) : row literal mode.gap false = transition false false mode.gap := by cases mode <;> decide +kernel
theorem retGapOne (mode : ReturnMode) : row literal mode.gap true = transition false false mode.finish := by cases mode <;> decide +kernel

end ReturnRows

open ReturnRows

private theorem returnAcrossBlock (mode : ReturnMode) (n l r : Nat) :
    Reaches literal
      (fromLeft mode.entry (push false (pack (List.replicate (n + 1) true) l)) r)
      (fromLeft mode.entry l (pack (List.replicate (n + 1) true) (push false r))) := by
  rw [pack_repeat_last true n (push false r)]
  rw [List.replicate_succ, pack_cons]
  exact (Reaches.left' (retZero mode) _ _).trans
    ((Reaches.left' (retOneZeroOne mode) _ _).trans (Reaches.scanLeft (retOne mode) n l _))

private theorem returnBlocks (mode : ReturnMode) (ns : List Nat) (l r : Nat) :
    Reaches literal
      (fromLeft mode.entry (pack (blocks ns).reverse l) r)
      (fromLeft mode.entry l (pack (blocks ns) r)) := by
  induction ns generalizing l r with
  | nil => exact ⟨0, rfl⟩
  | cons n ns ih =>
    simp only [blocks, List.reverse_append, List.reverse_cons, List.reverse_replicate, pack_append]
    simpa only [pack_cons, pack_nil] using
      (ih (push false (pack (List.replicate (n + 1) true) l)) r).trans
        (returnAcrossBlock mode n l (pack (blocks ns) r))

private theorem returnGapScan (mode : ReturnMode) (n l r : Nat) :
    Reaches literal
      (fromLeft mode.gap (pack (List.replicate n false) (push true l)) r)
      (fromLeft mode.finish l (pack (List.replicate (n + 1) false) r)) := by
  rw [List.replicate_succ, pack_cons]
  exact (Reaches.scanLeft (retGapZero mode) n (push true l) r).trans (Reaches.left' (retGapOne mode) l _)

/-- The common successful return routine. It crosses the reversed register
prefix and gap, then clears the temporary marker. -/
theorem return_over_mode (mode : ReturnMode) (gap : Nat) (ns : List Nat) (l r : Nat) :
    Reaches literal
      (fromLeft mode.entry (pack (blocks ns).reverse
        (pack (List.replicate (gap + 2) false) (push true l))) r)
      (fromLeft mode.finish l (pack (List.replicate (gap + 3) false ++ blocks ns) r)) := by
  have through := returnBlocks mode ns (pack (List.replicate (gap + 2) false) (push true l)) r
  refine through.trans ?_
  simp only [pack_append]
  have start : pack (List.replicate (gap + 2) false) (push true l) =
      push false (push false (pack (List.replicate gap false) (push true l))) := by
    rw [show gap + 2 = (gap + 1) + 1 by omega]
    simp only [List.replicate_succ, pack_cons]
  rw [start]
  refine (Reaches.left' (retZero mode) _ _).trans ((Reaches.left' (retOneZeroZero mode) _ _).trans ?_)
  have finish := returnGapScan mode gap l (push false (push false (pack (blocks ns) r)))
  rw [show gap + 3 = (gap + 1 + 1) + 1 by omega, pack_repeat_last, pack_repeat_last]
  exact finish

theorem scan_return_ones (mode : ReturnMode) (n l r : Nat) :
    Reaches literal (fromLeft mode.entry (pack (List.replicate n true) l) r)
      (fromLeft mode.entry l (pack (List.replicate n true) r)) :=
  Reaches.scanLeft (retOne mode) n l r

theorem return_over (gap : Nat) (ns : List Nat) (l r : Nat) :
    Reaches literal
      (fromLeft returnStart (pack (blocks ns).reverse
        (pack (List.replicate (gap + 2) false) (push true l))) r)
      (fromLeft breakZero l (pack (List.replicate (gap + 3) false ++ blocks ns) r)) :=
  return_over_mode .success gap ns l r

/-- Increment increases the selected unary word on its left edge and
returns to the instruction pointer. The gap has at least two cells
between the temporary marker and the register prefix. -/
theorem increment_selected (gap n : Nat) (ns : List Nat) (l r : Nat) :
    Reaches literal
      ⟨increment, l, push false (pack (List.replicate (gap + 2) false ++ blocks (n :: ns))
        (push false r))⟩
      (fromLeft breakZero l
        (pack (List.replicate (gap + 3) false ++ blocks (n :: ns)) (push true r))) :=
  (increment_forward (gap + 2) n ns l r).trans (return_over gap (n :: ns) l (push true r))

end I0451.Runtime
