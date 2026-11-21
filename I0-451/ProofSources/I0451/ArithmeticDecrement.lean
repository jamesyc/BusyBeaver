module
public import I0451.ArithmeticRegisters
public import I0451.RegisterDecrement

/-! The success and failure paths of the literal decrement routine. -/

@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Runtime I0451.Runtime.DecrementRows

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] modelRepeat modelPush modelConfig modelFromLeft trace

private theorem across_block {q : Nat} (entry : row literal q true = transition false true decOnes)
    (n l r : V) :
    ModelReaches literal (modelConfig q l (modelBlocks [n] r))
      (modelConfig decSeparator (modelRepeat true (n + 1) (modelPush false l)) r) := by
  simp only [modelBlocks, modelRepeat_succ]
  exact (ModelReaches.right entry l _).trans
    ((ModelReaches.scanRight onesOne n (modelPush false l) _).trans
      (ModelReaches.right onesZero _ _))

private theorem shift_prefix (ns : List V) (l r : V) :
    ModelReaches literal (modelConfig decSeparator l (modelBlocks ns (modelPush false r)))
      (modelConfig decSeek (modelReverseBlocks ns (modelPush false l)) r) := by
  induction ns generalizing l with
  | nil => exact ModelReaches.right sepZero ..
  | cons x xs ih =>
    exact (across_block sepOne x l (modelBlocks xs (modelPush false r))).trans
      (ih (modelRepeat true (x + 1) (modelPush false l)))

private theorem shift_entry (gap n : V) (ns : List V) (l r : V) :
    ModelReaches literal
      (modelConfig decrement l (modelPush false (modelRepeat false (gap + 1 + 1)
        (modelBlocks (n :: ns) (modelPush false r)))))
      (modelConfig decSeek
        (modelReverseBlocks (n :: ns) (modelRepeat false (gap + 1 + 1 + 1) (modelPush true l))) r) := by
  let gapLeft := modelRepeat false (gap + 1 + 1) (modelPush true l)
  let body := modelBlocks (n :: ns) (modelPush false r)
  have first := ModelReaches.right decEntry l (modelRepeat false (gap + 1 + 1) body)
  have crossed := ModelReaches.scanRight gapZero (gap + 1 + 1) (modelPush true l) body
  have blocks : ModelReaches literal (modelConfig decGap gapLeft body)
      (modelConfig decSeek (modelReverseBlocks (n :: ns) (modelPush false gapLeft)) r) :=
    (across_block gapOne n gapLeft (modelBlocks ns (modelPush false r))).trans
      (shift_prefix ns (modelRepeat true (n + 1) (modelPush false gapLeft)) r)
  rw [modelRepeat_succ false (gap + 1 + 1) (modelPush true l)]
  exact first.trans (crossed.trans blocks)

private theorem inspect_target (n l r : V) :
    ModelReaches literal (modelConfig decSeek l (modelRepeat true (n + 1) (modelPush false r)))
      (modelFromLeft decInspect (modelRepeat true n l) (modelPush true (modelPush false r))) := by
  have scan := ModelReaches.scanRight seekOne (n + 1) l (modelPush false r)
  have turned := ModelReaches.enterLeft seekZero (modelPush true (modelRepeat true n l)) r
  have check := ModelReaches.moveLeft decBackOne (modelRepeat true n l) (modelPush false r)
  rw [modelRepeat_succ true n l] at scan
  exact scan.trans (turned.trans check)

private theorem shift_suffix (ns : List V) (l : V) :
    ModelReaches literal (modelConfig decShift l (modelPush false (modelBlocks ns 0)))
      (modelFromLeft returnStart (modelReverseBlocks ns l) 0) := by
  induction ns generalizing l with
  | nil =>
    simpa only [modelBlocks, modelReverseBlocks, modelPush_false_zero] using
      (ModelReaches.right shiftZero l 0).trans
      ((show ModelReaches literal (modelConfig decCheckTail (modelPush true l) (0 : V))
          (modelFromLeft select (modelPush true l) 0) from by
            simpa only [modelPush_false_zero] using ModelReaches.enterLeft checkZero (modelPush true l) (0 : V)).trans
        (ModelReaches.moveLeft removeLast l (0 : V)))
  | cons n ns ih =>
    let tail := modelBlocks ns (0 : V)
    let written := modelRepeat true n l
    have first := ModelReaches.right shiftZero l
      (modelPush true (modelRepeat true n (modelPush false tail)))
    have entry := ModelReaches.right checkOne (modelPush true l)
      (modelRepeat true n (modelPush false tail))
    have scanned := ModelReaches.scanRight seekOne n (modelPush true (modelPush true l))
      (modelPush false tail)
    rw [modelRepeat_push, modelRepeat_push] at scanned
    have turned := ModelReaches.enterLeft seekZero (modelPush true (modelPush true written)) tail
    have inspect := ModelReaches.moveLeft decBackOne (modelPush true written) (modelPush false tail)
    have next := ModelReaches.leaveLeft inspectOne written (modelPush true (modelPush false tail))
    have clear := ModelReaches.right shiftOne (modelPush true written) (modelPush false tail)
    have rest := ih (modelPush false (modelPush true written))
    simpa only [modelBlocks, modelReverseBlocks, modelRepeat_succ, written, tail] using
      first.trans (entry.trans (scanned.trans (turned.trans (inspect.trans (next.trans (clear.trans rest))))))

theorem model_decrement_positive (gap x n : V) (xs following : List V) (l : V) :
    ModelReaches literal
      (modelConfig decrement l (modelPush false (modelRepeat false (gap + 1 + 1)
        (modelBlocks (x :: xs) (modelPush false (modelBlocks ((n + 1) :: following) 0))))))
      (modelFromLeft breakZero l
        (modelRepeat false (gap + 1 + 1 + 1 + 1) (modelBlocks ((x :: xs) ++ n :: following) 0))) := by
  let shifted := modelReverseBlocks (x :: xs)
    (modelRepeat false (gap + 1 + 1 + 1) (modelPush true l))
  let tail := modelBlocks following (0 : V)
  have entry := shift_entry gap x xs l (modelBlocks ((n + 1) :: following) 0)
  have examine := inspect_target (n + 1) shifted tail
  rw [modelRepeat_succ true n shifted] at examine
  have jump := ModelReaches.leaveLeft inspectOne (modelRepeat true n shifted)
    (modelPush true (modelPush false tail))
  have clear := ModelReaches.right shiftOne (modelPush true (modelRepeat true n shifted))
    (modelPush false tail)
  have shiftedRest := shift_suffix following (modelPush false (modelPush true (modelRepeat true n shifted)))
  have finish := model_return_over .success (gap + 1) ((x :: xs) ++ n :: following) l 0
  rw [modelReverseBlocks_append] at finish
  simp only [modelReverseBlocks, modelRepeat_succ true n, ReturnMode.entry, ReturnMode.finish] at finish
  exact entry.trans (examine.trans (jump.trans (clear.trans (shiftedRest.trans finish))))

theorem model_decrement_zero (gap last : V) (before following : List V) (l : V) :
    ModelReaches literal
      (modelConfig decrement l (modelPush false (modelRepeat false (gap + 1 + 1)
        (modelBlocks (before ++ [last]) (modelPush false (modelBlocks (0 :: following) 0))))))
      (modelFromLeft breakOne l
        (modelRepeat false (gap + 1 + 1 + 1 + 1)
          (modelBlocks (before ++ last :: 0 :: following) 0))) := by
  let gapLeft := modelRepeat false (gap + 1 + 1 + 1) (modelPush true l)
  let leftPrefix := modelReverseBlocks before gapLeft
  let leftOnes := modelRepeat true (last + 1) leftPrefix
  let tail := modelBlocks following (0 : V)
  have entry : ModelReaches literal
      (modelConfig decrement l (modelPush false (modelRepeat false (gap + 1 + 1)
        (modelBlocks (before ++ [last]) (modelPush false (modelBlocks (0 :: following) 0))))))
      (modelConfig decSeek (modelReverseBlocks (before ++ [last]) gapLeft)
        (modelBlocks (0 :: following) 0)) := by
    cases before with
    | nil => exact shift_entry gap last [] l _
    | cons b bs => exact shift_entry gap b (bs ++ [last]) l _
  have layout : modelReverseBlocks (before ++ [last]) gapLeft = modelPush false leftOnes := by
    rw [modelReverseBlocks_append]
    rfl
  rw [layout] at entry
  have examine := inspect_target 0 (modelPush false leftOnes) tail
  rw [modelRepeat_zero] at examine
  have failed := ModelReaches.moveLeft inspectZero leftOnes (modelPush true (modelPush false tail))
  have across := ModelReaches.scanLeft (ReturnRows.retOne .failure) (last + 1) leftPrefix
    (modelPush false (modelPush true (modelPush false tail)))
  have finish := model_return_over .failure (gap + 1) before l
    (modelRepeat true (last + 1) (modelPush false (modelPush true (modelPush false tail))))
  rw [modelBlocks_append before (last :: 0 :: following) (0 : V)]
  simpa only [modelBlocks, modelRepeat_succ true (0 : V), modelRepeat_zero, ReturnMode.finish, tail] using
    entry.trans (examine.trans (failed.trans (across.trans finish)))

end I0451.Arithmetization
