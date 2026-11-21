module
public import I0451.ArithmeticRegisters
public import I0451.RegisterSelect

/-! Moving the selector delimiter across a model-valued register. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Runtime I0451.Runtime.SelectRows

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] modelRepeat modelPush modelFromLeft modelConfig trace

private theorem scan_block {q : Nat} (entry : row literal q true = transition true true selectOnes)
    (n l r : V) :
    ModelReaches literal (modelConfig q l (modelBlocks [n] r))
      (modelConfig selectSeparator (modelReverseBlocks [n] l) r) := by
  simp only [modelBlocks, modelReverseBlocks]
  rw [modelRepeat_succ true n (modelPush false r), modelRepeat_succ true n l,
    ← modelRepeat_push true n l]
  exact (ModelReaches.right entry l _).trans
    ((ModelReaches.scanRight scanOne n (modelPush true l) _).trans (ModelReaches.right scanZero _ _))

private theorem scan_blocks (ns : List V) (l r : V) :
    ModelReaches literal (modelConfig selectSeparator l (modelBlocks ns r))
      (modelConfig selectSeparator (modelReverseBlocks ns l) r) := by
  induction ns generalizing l with
  | nil => exact ModelReaches.refl literal _
  | cons n ns ih =>
    exact (scan_block sepOne n l (modelBlocks ns r)).trans
      (ih (modelReverseBlocks [n] l))

private theorem reverse_separator (x : V) (xs : List V) (tail : V) :
    ∃ body, modelReverseBlocks (x :: xs) tail = modelPush false body := by
  induction xs generalizing x tail with
  | nil => exact ⟨_, rfl⟩
  | cons b bs ih =>
    exact ih b (modelPush false (modelRepeat true (x + 1) tail))

private theorem shift_boundary (gap x : V) (xs : List V) (u l r : V) :
    ModelReaches literal
      (modelConfig select l (modelPush false (modelRepeat false (gap + 1 + 1)
        (modelBlocks ((x :: xs) ++ [u]) (modelPush false r)))))
      (modelFromLeft returnStart
        (modelReverseBlocks (x :: xs) (modelRepeat false (gap + 1 + 1) (modelPush true l)))
        (modelPush false (modelBlocks [u] r))) := by
  let leftGap := modelRepeat false (gap + 1 + 1) (modelPush true l)
  let leftPrefix := modelReverseBlocks (x :: xs) leftGap
  let rightBlock := modelBlocks [u] (modelPush false r)
  rw [modelBlocks_append]
  have initial := (ModelReaches.right selectEntry l (modelRepeat false (gap + 1 + 1)
    (modelBlocks (x :: xs) rightBlock))).trans
    (ModelReaches.scanRight gapZero (gap + 1 + 1) (modelPush true l) (modelBlocks (x :: xs) rightBlock))
  have across : ModelReaches literal (modelConfig selectGap leftGap (modelBlocks (x :: xs) rightBlock))
      (modelConfig selectSeparator leftPrefix rightBlock) :=
    (scan_block gapOne x leftGap (modelBlocks xs rightBlock)).trans
      (scan_blocks xs (modelReverseBlocks [x] leftGap) rightBlock)
  have beforeShift := scan_block sepOne u leftPrefix (modelPush false r)
  have turn := (ModelReaches.enterLeft sepZero (modelReverseBlocks [u] leftPrefix) r).trans
    (ModelReaches.moveLeft backZero (modelRepeat true (u + 1) leftPrefix) (modelPush false r))
  have backward := ModelReaches.scanLeft reverseOne (u + 1) leftPrefix (modelPush true (modelPush false r))
  rw [modelRepeat_push true (u + 1) (modelPush false r)] at backward
  have returnLeg :
      ModelReaches literal
        (modelFromLeft selectReverse leftPrefix (modelPush true (modelBlocks [u] r)))
        (modelFromLeft returnStart leftPrefix (modelPush false (modelBlocks [u] r))) := by
    obtain ⟨body, eq⟩ := reverse_separator x xs leftGap
    rw [show leftPrefix = modelPush false body from eq]
    exact (ModelReaches.leaveLeft reverseZero body (modelPush true (modelBlocks [u] r))).trans
      (ModelReaches.enterLeft backOne (modelPush false body) (modelBlocks [u] r))
  exact initial.trans (across.trans (beforeShift.trans (turn.trans (backward.trans returnLeg))))

theorem model_select_preceding (gap x : V) (xs : List V) (u l r : V) :
    ModelReaches literal
      (modelConfig select l (modelPush false (modelRepeat false (gap + 1 + 1)
        (modelBlocks ((x :: xs) ++ [u]) (modelPush false r)))))
      (modelFromLeft breakZero l (modelRepeat false (gap + 1 + 1 + 1)
        (modelBlocks (x :: xs) (modelPush false (modelBlocks [u] r))))) :=
  (shift_boundary gap x xs u l r).trans
    (model_return_over .success gap (x :: xs) l (modelPush false (modelBlocks [u] r)))

end I0451.Arithmetization
