module
public import I0451.RegisterIncrement

/-! Decrement on a selected register. The outward scan shifts the
preceding blocks one cell right. Successful decrement shifts the
following blocks left and removes the temporary last register. -/

@[expose] public section
namespace I0451.Runtime

namespace DecrementRows

theorem decEntry : row literal decrement false = transition true true decGap := by decide +kernel
theorem decBackOne : row literal decrement true = transition true false decInspect := by decide +kernel
theorem gapZero : row literal decGap false = transition false true decGap := by decide +kernel
theorem gapOne : row literal decGap true = transition false true decOnes := by decide +kernel
theorem onesOne : row literal decOnes true = transition true true decOnes := by decide +kernel
theorem onesZero : row literal decOnes false = transition true true decSeparator := by decide +kernel
theorem sepOne : row literal decSeparator true = transition false true decOnes := by decide +kernel
theorem sepZero : row literal decSeparator false = transition false true decSeek := by decide +kernel
theorem seekOne : row literal decSeek true = transition true true decSeek := by decide +kernel
theorem seekZero : row literal decSeek false = transition false false decrement := by decide +kernel
theorem inspectZero : row literal decInspect false = transition false false returnFail := by decide +kernel
theorem inspectOne : row literal decInspect true = transition true true decShift := by decide +kernel
theorem shiftZero : row literal decShift false = transition true true decCheckTail := by decide +kernel
theorem shiftOne : row literal decShift true = transition false true decShift := by decide +kernel
theorem checkZero : row literal decCheckTail false = transition false false select := by decide +kernel
theorem checkOne : row literal decCheckTail true = transition true true decSeek := by decide +kernel
theorem removeLast : row literal select true = transition false false returnStart := by decide +kernel

end DecrementRows

open DecrementRows

private theorem acrossBlock {q : Nat} (entry : row literal q true = transition false true decOnes)
    (n l r : Nat) :
    Reaches literal ⟨q, l, pack (blocks [n]) r⟩
      ⟨decSeparator, pack (List.replicate (n + 1) true) (push false l), r⟩ := by
  have first := Reaches.right entry l (pack (List.replicate n true) (push false r))
  have middle : Reaches literal _ _ :=
    ⟨n, scan_right onesOne n (push false l) (push false r)⟩
  have all := first.trans (middle.trans (Reaches.right onesZero _ _))
  simpa [blocks, List.replicate_succ, pack_append] using all

private theorem shiftPrefix (ns : List Nat) (l r : Nat) :
    Reaches literal ⟨decSeparator, l, pack (blocks ns) (push false r)⟩
      ⟨decSeek, pack (blocks ns).reverse (push false l), r⟩ := by
  induction ns generalizing l with
  | nil => exact Reaches.right sepZero l r
  | cons x xs ih =>
    rw [show x :: xs = [x] ++ xs from rfl, blocks_append, List.reverse_append,
      pack_append, pack_append]
    have first := acrossBlock sepOne x l (pack (blocks xs) (push false r))
    have rest := ih (pack (List.replicate (x + 1) true) (push false l))
    have tape : pack (blocks [x]).reverse (push false l) =
        push false (pack (List.replicate (x + 1) true) (push false l)) := by
      simp [blocks, List.reverse_append]
    rw [tape]
    exact first.trans rest

private theorem shiftEntry (gap n : Nat) (ns : List Nat) (l r : Nat) :
    Reaches literal
      ⟨decrement, l, push false
        (pack (List.replicate (gap + 2) false ++ blocks (n :: ns)) (push false r))⟩
      ⟨decSeek, pack (blocks (n :: ns)).reverse
        (pack (List.replicate (gap + 3) false) (push true l)), r⟩ := by
  let gapLeft := pack (List.replicate (gap + 2) false) (push true l)
  simp only [pack_append]
  let body := pack (blocks (n :: ns)) (push false r)
  have first := Reaches.right decEntry l (pack (List.replicate (gap + 2) false) body)
  have gapRun : Reaches literal _ _ :=
    ⟨gap + 2, scan_right gapZero _ (push true l) body⟩
  have across : Reaches literal ⟨decGap, gapLeft, body⟩
      ⟨decSeek, pack (blocks (n :: ns)).reverse (push false gapLeft), r⟩ := by
    have expand : n :: ns = [n] ++ ns := rfl
    simp only [body, expand, blocks_append, List.reverse_append, pack_append]
    have firstBlock := acrossBlock gapOne n gapLeft (pack (blocks ns) (push false r))
    have rest := shiftPrefix ns (pack (List.replicate (n + 1) true) (push false gapLeft)) r
    have tape : pack (blocks [n]).reverse (push false gapLeft) =
        push false (pack (List.replicate (n + 1) true) (push false gapLeft)) := by
      simp [blocks, List.reverse_append]
    rw [tape]
    exact firstBlock.trans rest
  have shape : pack (List.replicate (gap + 3) false) (push true l) = push false gapLeft := by
    rw [show gap + 3 = (gap + 2) + 1 by omega, List.replicate_succ, pack_cons]
  rw [shape]
  exact first.trans (gapRun.trans across)

private theorem inspectTarget (n l r : Nat) :
    Reaches literal ⟨decSeek, l, pack (List.replicate (n + 1) true) (push false r)⟩
      (fromLeft decInspect (pack (List.replicate n true) l) (push true (push false r))) := by
  have scan : Reaches literal _ _ :=
    ⟨n + 1, scan_right seekOne (n + 1) l (push false r)⟩
  have turn := Reaches.enterLeft seekZero
    (push true (pack (List.replicate n true) l)) r
  have check := Reaches.left' decBackOne (pack (List.replicate n true) l) (push false r)
  have combined := turn.trans check
  have tape : pack (List.replicate (n + 1) true) l =
      push true (pack (List.replicate n true) l) := by rw [List.replicate_succ, pack_cons]
  rw [← tape] at combined
  exact scan.trans combined

private theorem shiftSuffix (ns : List Nat) (l : Nat) :
    Reaches literal ⟨decShift, l, push false (pack (blocks ns) 0)⟩
      (fromLeft returnStart (pack (blocks ns).reverse l) 0) := by
  induction ns generalizing l with
  | nil =>
    have x := Reaches.right shiftZero l 0
    have y := Reaches.enterLeft checkZero (push true l) 0
    have z := Reaches.left' removeLast l 0
    exact x.trans (y.trans z)
  | cons n ns ih =>
    let tail := pack (blocks ns) 0
    have first := Reaches.right shiftZero l (push true (pack (List.replicate n true) (push false tail)))
    have entry := Reaches.right checkOne (push true l) (pack (List.replicate n true) (push false tail))
    have scan : Reaches literal _ _ :=
      ⟨n, scan_right seekOne n (push true (push true l)) (push false tail)⟩
    have leftTape : pack (List.replicate n true) (push true (push true l)) =
        push true (push true (pack (List.replicate n true) l)) := by
      rw [← pack_repeat_last, List.replicate_succ, pack_cons,
        ← pack_repeat_last, List.replicate_succ, pack_cons]
    have turn := Reaches.enterLeft seekZero (push true (push true (pack (List.replicate n true) l))) tail
    have inspect := Reaches.left' decBackOne (push true (pack (List.replicate n true) l)) (push false tail)
    have next := Reaches.leaveLeft inspectOne (pack (List.replicate n true) l) (push true (push false tail))
    have clear := Reaches.right shiftOne (push true (pack (List.replicate n true) l)) (push false tail)
    have rest := ih (push false (push true (pack (List.replicate n true) l)))
    rw [leftTape] at scan
    have joined := scan.trans (turn.trans (inspect.trans (next.trans (clear.trans rest))))
    simpa [blocks, List.replicate_succ, List.reverse_append, pack_append, tail, ← pack_repeat_last] using
      first.trans (entry.trans joined)

/-- Positive decrement after the selector has reached the specified
register. The decoded value drops by one and the gap gains one cell. -/
theorem decrement_positive (gap x n : Nat) (xs following : List Nat) (l : Nat) :
    Reaches literal
      ⟨decrement, l, push false
        (pack (List.replicate (gap + 2) false ++ blocks (x :: xs))
          (push false (pack (blocks ((n + 1) :: following)) 0)))⟩
      (fromLeft breakZero l
        (pack (List.replicate (gap + 4) false ++ blocks ((x :: xs) ++ n :: following)) 0)) := by
  let shifted := pack (blocks (x :: xs)).reverse
    (pack (List.replicate (gap + 3) false) (push true l))
  let tail := pack (blocks following) 0
  have entry := shiftEntry gap x xs l (pack (blocks ((n + 1) :: following)) 0)
  have examine : Reaches literal ⟨decSeek, shifted, pack (blocks ((n + 1) :: following)) 0⟩
      (fromLeft decInspect (push true (pack (List.replicate n true) shifted))
        (push true (push false tail))) := by
    simpa [blocks, tail, pack_append, pack_repeat_last, List.replicate_succ] using
      inspectTarget (n + 1) shifted tail
  have jump := Reaches.leaveLeft inspectOne (pack (List.replicate n true) shifted)
    (push true (push false tail))
  have clear := Reaches.right shiftOne (push true (pack (List.replicate n true) shifted)) (push false tail)
  have shiftedRest := shiftSuffix following (push false (push true (pack (List.replicate n true) shifted)))
  have finish := return_over (gap + 1) ((x :: xs) ++ n :: following) l 0
  have tape : pack (blocks ((x :: xs) ++ n :: following)).reverse
      (pack (List.replicate (gap + 3) false) (push true l)) =
      pack (blocks following).reverse
        (push false (push true (pack (List.replicate n true) shifted))) := by
    have split : (x :: xs) ++ n :: following = (x :: xs) ++ ([n] ++ following) := rfl
    rw [split, blocks_append, blocks_append, List.reverse_append, List.reverse_append,
      pack_append, pack_append]
    simp [blocks, List.reverse_append, pack_append, List.replicate_succ, shifted,
      ← pack_repeat_last]
  rw [tape] at finish
  exact entry.trans (examine.trans (jump.trans (clear.trans (shiftedRest.trans finish))))

/-- A zero register is left at zero. The failure return control is
`breakOne`, with the same one-cell increase in gap as in the positive case. -/
theorem decrement_zero (gap last : Nat) (before following : List Nat) (l : Nat) :
    Reaches literal
      ⟨decrement, l, push false
        (pack (List.replicate (gap + 2) false ++ blocks (before ++ [last]))
          (push false (pack (blocks (0 :: following)) 0)))⟩
      (fromLeft breakOne l
        (pack (List.replicate (gap + 4) false ++ blocks (before ++ last :: 0 :: following)) 0)) := by
  let gapLeft := pack (List.replicate (gap + 3) false) (push true l)
  let leftPrefix := pack (blocks before).reverse gapLeft
  let leftOnes := pack (List.replicate (last + 1) true) leftPrefix
  let tail := pack (blocks following) 0
  have entry : Reaches literal
      ⟨decrement, l, push false
        (pack (List.replicate (gap + 2) false ++ blocks (before ++ [last]))
          (push false (pack (blocks (0 :: following)) 0)))⟩
      ⟨decSeek, pack (blocks (before ++ [last])).reverse gapLeft,
        pack (blocks (0 :: following)) 0⟩ := by
    cases before with
    | nil => exact shiftEntry gap last [] l _
    | cons x xs => exact shiftEntry gap x (xs ++ [last]) l _
  have layout : pack (blocks (before ++ [last])).reverse gapLeft =
      push false leftOnes := by
    simp [blocks_append, List.reverse_append, pack_append, blocks, leftOnes, leftPrefix]
  rw [layout] at entry
  have examine : Reaches literal ⟨decSeek, push false leftOnes, pack (blocks (0 :: following)) 0⟩
      (fromLeft decInspect (push false leftOnes) (push true (push false tail))) := by
    simpa [blocks, tail] using inspectTarget 0 (push false leftOnes) tail
  have jump := Reaches.left' inspectZero leftOnes (push true (push false tail))
  have lastBlock := scan_return_ones .failure (last + 1) leftPrefix
    (push false (push true (push false tail)))
  have finish := return_over_mode .failure (gap + 1) before l
    (pack (List.replicate (last + 1) true) (push false (push true (push false tail))))
  have rest : pack (blocks (before ++ last :: 0 :: following)) 0 =
      pack (blocks before)
        (pack (List.replicate (last + 1) true) (push false (push true (push false tail)))) := by
    simp [blocks_append, pack_append, blocks, tail]
  simp only [pack_append] at finish ⊢
  rw [rest]
  simpa only [pack_append, ReturnMode.finish] using
    entry.trans (examine.trans (jump.trans (lastBlock.trans finish)))

end I0451.Runtime
