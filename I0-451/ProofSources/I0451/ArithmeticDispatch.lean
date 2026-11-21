module
public import I0451.ArithmeticDecoder
public import I0451.Dispatch

/-! The address changes in the literal machine. Program addresses are
standard finite words, while the register file beyond them is arbitrary. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Runtime I0451.Runtime.DispatchRows

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] trace

private theorem dispatch_word {n : Nat} {word : List Bool} (hn : n ≤ 7)
    (safe : SafeDispatch n word) (l r : V) :
    ModelReaches literal (modelFromLeft (dispatch n) (modelPack word l) r)
      (modelFromLeft (dispatch (dispatchEnd n word)) l (modelPack word.reverse r)) := by
  induction word generalizing n r with
  | nil => exact ModelReaches.refl literal _
  | cons b rest ih =>
    simp only [modelPack_cons, List.reverse_cons, modelPack_append, modelPack_nil, dispatchEnd]
    exact (ModelReaches.moveLeft (dispatchRow hn safe.1) _ _).trans
      (ih safe.1 safe.2 (modelPush b r))

private theorem zero_word (n : Nat) : modelPack (List.replicate n false) (0 : V) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih, modelPush]

private theorem marker : modelPush true (0 : V) = 1 := by simp [modelPush]

private theorem fromLeft_zero (q : Nat) (r : V) :
    modelFromLeft q 0 r = modelConfig q 0 (modelPush false r) := by
  simpa only [modelPush, mul_zero, Bool.toNat_false, Nat.cast_zero, add_zero] using
    modelFromLeft_push q false (0 : V) r

private theorem model_bounce (r : V) :
    ModelReaches literal (modelFromLeft continueZero 0 (modelPush true r))
      (modelConfig root 1 r) := by
  have bounce := ModelReaches.window bounce_window (0 : V) r
  change ModelReaches literal
    (modelConfig continueZero (modelPack (List.replicate 7 false) 0)
      (modelPush false (modelPush true r)))
    (modelConfig root (modelPush true (modelPack (List.replicate 8 false) 0)) r) at bounce
  simpa only [zero_word, marker, fromLeft_zero] using bounce

theorem model_continue_zero {word : List Bool} (safe : SafeDispatch 0 word.reverse) (r : V) :
    ModelReaches literal (modelFromLeft continueZero (modelPack word.reverse 1) r)
      (modelConfig root 1 (modelPack word r)) := by
  have scan := dispatch_word (n := 0) (by decide) safe (1 : V) r
  rw [dispatch_zero, List.reverse_reverse] at scan
  have count := safeEnd (n := 0) (by decide) safe
  have through : ModelReaches literal
      (modelFromLeft (dispatch (dispatchEnd 0 word.reverse)) 1 (modelPack word r))
      (modelFromLeft continueZero 0 (modelPush true (modelPack word r))) := by
    rw [← marker]
    exact ModelReaches.moveLeft (onesRow ⟨_, by omega⟩) 0 _
  exact scan.trans (through.trans (model_bounce _))

theorem model_break_zero {reversed : List Bool} (safe : SafeDispatch 0 reversed) (r : V) :
    ModelReaches literal (modelFromLeft breakZero (modelPack reversed 1) r)
      (modelConfig root 1 (modelPack (carry reversed).reverse r)) := by
  induction reversed generalizing r with
  | nil =>
    simp only [modelPack_nil, carry, List.reverse_singleton, modelPack_cons]
    have erase : ModelReaches literal (modelFromLeft breakZero 1 r)
        (modelFromLeft breakZero 0 (modelPush false r)) := by
      rw [← marker]
      exact ModelReaches.moveLeft breakOneBit 0 r
    have restore : ModelReaches literal (modelFromLeft breakZero 0 (modelPush false r))
        (modelFromLeft continueZero 0 (modelPush true (modelPush false r))) := by
      rw [show modelFromLeft breakZero 0 (modelPush false r) =
          modelFromLeft breakZero (modelPush false 0) (modelPush false r) by simp [modelPush]]
      exact ModelReaches.moveLeft breakZeroBit 0 _
    exact erase.trans (restore.trans (model_bounce _))
  | cons b rest ih =>
    cases b with
    | false =>
      simp only [carry, List.reverse_cons, modelPack_append, modelPack_cons, modelPack_nil]
      have move := ModelReaches.moveLeft breakZeroBit (modelPack rest (1 : V)) r
      have continued := model_continue_zero (word := rest.reverse)
        (by simpa only [List.reverse_reverse] using safe.tail) (modelPush true r)
      rw [List.reverse_reverse] at continued
      exact move.trans continued
    | true =>
      simp only [carry, List.reverse_cons, modelPack_append, modelPack_cons, modelPack_nil]
      exact (ModelReaches.moveLeft breakOneBit _ _).trans (ih safe.tail (modelPush false r))

theorem model_break_one {reversed : List Bool} (safe : SafeDispatch 0 reversed) (ones r : V) :
    ModelReaches literal
      (modelFromLeft breakOne (modelRepeat true ones (modelPush false (modelPack reversed 1))) r)
      (modelConfig root 1 (modelPack (carry reversed).reverse (modelPush false (modelRepeat false ones r)))) :=
  (ModelReaches.scanLeft breakSkipOne ones _ _).trans
    ((ModelReaches.moveLeft breakSkipZero _ _).trans (model_break_zero safe _))

theorem model_continue_one {reversed : List Bool} (safe : SafeDispatch 0 reversed) (zeros r : V) :
    ModelReaches literal
      (modelFromLeft continueOne (modelRepeat false zeros (modelPush true (modelPack reversed 1))) r)
      (modelConfig root 1 (modelPack reversed.reverse (modelPush false (modelRepeat false zeros r)))) := by
  have enter := ModelReaches.scanLeft continueSkipZero zeros (modelPush true (modelPack reversed 1)) r
  have clear := ModelReaches.moveLeft continueSkipOne (modelPack reversed 1) (modelRepeat false zeros r)
  have back := model_continue_zero (word := reversed.reverse)
    (by simpa only [List.reverse_reverse] using safe) (modelPush false (modelRepeat false zeros r))
  rw [List.reverse_reverse] at back
  exact enter.trans (clear.trans back)

end I0451.Arithmetization
