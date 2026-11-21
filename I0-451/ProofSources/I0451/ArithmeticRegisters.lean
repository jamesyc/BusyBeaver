module
public import I0451.ArithmeticDecoder
public import I0451.RegisterIncrement

/-! Blocks of the literal register file contain unary lengths in the
arithmetic model. Increment and the common return path are lifted using
the individually checked literal rows. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] modelRepeat modelPush modelConfig modelFromLeft trace

/-- Connect the blocks in their ordinary order. -/
noncomputable def modelBlocks : List V → V → V
  | [], tail => tail
  | n :: rest, tail => modelRepeat true (n + 1) (modelPush false (modelBlocks rest tail))

/-- Connect the blocks in the bit order seen from their other edge. -/
noncomputable def modelReverseBlocks : List V → V → V
  | [], tail => tail
  | n :: rest, tail => modelReverseBlocks rest (modelPush false (modelRepeat true (n + 1) tail))

theorem modelBlocks_append (xs ys : List V) (tail : V) :
    modelBlocks (xs ++ ys) tail = modelBlocks xs (modelBlocks ys tail) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append, modelBlocks, ih]

theorem modelReverseBlocks_append (xs ys : List V) (tail : V) :
    modelReverseBlocks (xs ++ ys) tail = modelReverseBlocks ys (modelReverseBlocks xs tail) := by
  induction xs generalizing tail with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append, modelReverseBlocks, ih]

private noncomputable def remainder (n : V) (ns : List V) (tail : V) : V :=
  modelRepeat true n (modelPush false (modelBlocks ns tail))

private theorem increment_ones (n l r : V) :
    ModelReaches literal
      (modelConfig incrementOnes l (modelRepeat true n (modelPush false r)))
      (modelConfig incrementSeparator (modelPush false (modelRepeat true n l)) r) :=
  (ModelReaches.scanRight IncrementRows.onesOne n l (modelPush false r)).trans
    (ModelReaches.right IncrementRows.onesZero _ _)

private theorem increment_remainder (n : V) (ns : List V) (l r : V) :
    ModelReaches literal
      (modelConfig incrementOnes l (remainder n ns (modelPush false r)))
      (modelFromLeft returnStart
        (modelReverseBlocks ns (modelPush false (modelRepeat true n l))) (modelPush true r)) := by
  induction ns generalizing n l with
  | nil =>
    exact (increment_ones n l (modelPush false r)).trans
      (ModelReaches.enterLeft IncrementRows.sepZero _ _)
  | cons k ks ih =>
    change ModelReaches literal
      (modelConfig incrementOnes l (modelRepeat true n (modelPush false
        (modelRepeat true (k + 1) (modelPush false (modelBlocks ks (modelPush false r)))))))
      (modelFromLeft returnStart
        (modelReverseBlocks ks (modelPush false (modelRepeat true (k + 1)
          (modelPush false (modelRepeat true n l))))) (modelPush true r))
    rw [modelRepeat_succ]
    refine (increment_ones n l _).trans ((ModelReaches.right IncrementRows.sepOne _ _).trans ?_)
    rw [modelRepeat_succ, ← modelRepeat_push]
    exact ih k _

theorem model_increment_forward (gap n : V) (ns : List V) (l r : V) :
    ModelReaches literal
      (modelConfig increment l (modelPush false
        (modelRepeat false gap (modelBlocks (n :: ns) (modelPush false r)))))
      (modelFromLeft returnStart
        (modelReverseBlocks (n :: ns) (modelRepeat false gap (modelPush true l))) (modelPush true r)) := by
  simp only [modelBlocks, modelReverseBlocks, modelRepeat_succ]
  refine (ModelReaches.right IncrementRows.entryZero l _).trans
    ((ModelReaches.scanRight IncrementRows.gapZero gap (modelPush true l) _).trans
      ((ModelReaches.right IncrementRows.gapOne _ _).trans ?_))
  rw [← modelRepeat_push]
  exact increment_remainder n ns _ r

private theorem return_across_block (mode : ReturnMode) (n l r : V) :
    ModelReaches literal
      (modelFromLeft mode.entry (modelPush false (modelRepeat true (n + 1) l)) r)
      (modelFromLeft mode.entry l (modelRepeat true (n + 1) (modelPush false r))) := by
  simp only [modelRepeat_succ]
  rw [← modelRepeat_push true n (modelPush false r)]
  exact (ModelReaches.moveLeft (ReturnRows.retZero mode) _ _).trans
    ((ModelReaches.moveLeft (ReturnRows.retOneZeroOne mode) _ _).trans
      (ModelReaches.scanLeft (ReturnRows.retOne mode) n _ _))

private theorem return_blocks (mode : ReturnMode) (ns : List V) (l r : V) :
    ModelReaches literal (modelFromLeft mode.entry (modelReverseBlocks ns l) r)
      (modelFromLeft mode.entry l (modelBlocks ns r)) := by
  induction ns generalizing l r with
  | nil => exact ModelReaches.refl literal _
  | cons n ns ih =>
    exact (ih (modelPush false (modelRepeat true (n + 1) l)) r).trans
      (return_across_block mode n l (modelBlocks ns r))

theorem model_return_over (mode : ReturnMode) (gap : V) (ns : List V) (l r : V) :
    ModelReaches literal
      (modelFromLeft mode.entry
        (modelReverseBlocks ns (modelRepeat false (gap + 1 + 1) (modelPush true l))) r)
      (modelFromLeft mode.finish l (modelRepeat false (gap + 1 + 1 + 1) (modelBlocks ns r))) := by
  refine (return_blocks mode ns _ r).trans ?_
  simp only [modelRepeat_succ]
  refine (ModelReaches.moveLeft (ReturnRows.retZero mode) _ _).trans
    ((ModelReaches.moveLeft (ReturnRows.retOneZeroZero mode) _ _).trans
      ((ModelReaches.scanLeft (ReturnRows.retGapZero mode) gap _ _).trans ?_))
  rw [← modelRepeat_push, ← modelRepeat_push]
  exact ModelReaches.moveLeft (ReturnRows.retGapOne mode) l _

theorem model_increment_selected (gap n : V) (ns : List V) (l r : V) :
    ModelReaches literal
      (modelConfig increment l (modelPush false
        (modelRepeat false (gap + 1 + 1) (modelBlocks (n :: ns) (modelPush false r)))))
      (modelFromLeft breakZero l
        (modelRepeat false (gap + 1 + 1 + 1) (modelBlocks (n :: ns) (modelPush true r)))) :=
  (model_increment_forward (gap + 1 + 1) n ns l r).trans
    (model_return_over .success gap (n :: ns) l (modelPush true r))

end I0451.Arithmetization
