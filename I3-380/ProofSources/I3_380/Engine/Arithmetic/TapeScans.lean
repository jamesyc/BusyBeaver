module
public import I3_380.Engine.Arithmetic.Tape
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def pushBitDef (b : Bool) : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “out tail. out = 2*tail+↑b.toNat”

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pushBitDef_eval (b : Bool) (y x : M) : (pushBitDef b).val.Evalb ![y,x] ↔ y = pushBit b x := by
  simp [pushBitDef,pushBit,numeral_eq_natCast]

noncomputable def bitIteration (b : Bool) : PR.Construction M (iterationBlueprint (pushBitDef b)) :=
  iterationConstruction (pushBitDef b) (pushBit b) (pushBitDef_eval b)

noncomputable def repeatBit (b : Bool) (n tail : M) : M :=
  (bitIteration b).result ![tail] n

@[simp] theorem repeatBit_zero (b : Bool) (tail : M) : repeatBit b 0 tail = tail := by
  unfold repeatBit
  rw [PR.Construction.result_zero]
  rfl

@[simp] theorem repeatBit_succ (b : Bool) (n tail : M) :
    repeatBit b (n+1) tail = pushBit b (repeatBit b n tail) := by
  unfold repeatBit
  rw [PR.Construction.result_succ]
  rfl

@[simp] theorem repeatBit_one (b : Bool) (tail : M) : repeatBit b 1 tail = pushBit b tail := by
  simpa only [zero_add,repeatBit_zero] using repeatBit_succ b (0 : M) tail

@[definability] instance repeatBit_definable (b : Bool) : 𝚺ᴬ₁-Function₂ (repeatBit (M := M) b) := by
  have exactGraph : 𝚺ᴬ₁-Function₂ (repeatBit (M := M) b) via
      (iterationBlueprint (pushBitDef b)).resultDef := by
    refine .mk fun v => ?_
    rw [Matrix.fun_eq_vec_three v]
    simp only [(bitIteration b).result_defined_iff,Matrix.cons_val_zero,Matrix.cons_val_succ,repeatBit]
    rfl
  exact exactGraph.to_definable

@[definability] theorem encode_definable : 𝚺ᴬ₁-Function₃ (encode (M := M)) := by
  unfold encode
  definability

@[definability] theorem fromLeft_definable (q : Nat) : 𝚺ᴬ₁-Function₂ (fromLeft (M := M) q) := by
  unfold fromLeft encode divIn remIn
  definability

/-- Arithmetic induction checks an entire path whose coordinates are
definable in the model. In particular its length can be nonstandard. -/
theorem clock_follows (m : Machine) (length : M) (path : M → M)
    (definition : 𝚺ᴬ₁-Function₁ path)
    (transition : ∀ i < length, tick m.workingStates m.packedRows (path i) = path (i+1)) :
    ∀ i ≤ length, clock m.workingStates m.packedRows i (path 0) = path i := by
  intro i
  induction i using ISigma1.sigma1_succ_induction with
  | zero => intro _; exact clock_zero _ _ _
  | succ i ih =>
    intro fits
    have before := succ_le_iff_lt.mp fits
    rw [clock_succ,ih (le_of_lt before),transition i before]
  | hP => definability

private theorem remaining_step {i n : M} (before : i < n) :
    n-i = (n-(i+1))+1 := by
  simpa only [zero_add,add_zero] using (sub_succ_add_succ before (0 : M)).symm

theorem scan_right {m : Machine} {q : Nat} {read write : Bool}
    (active : q < m.workingStates) (row : m.row q read.toNat = 4*q+2*write.toNat+1)
    (n l r : M) :
    clock m.workingStates m.packedRows n (encode (q : M) l (repeatBit read n r)) =
      encode (q : M) (repeatBit write n l) r := by
  let path (i : M) := encode (q : M) (repeatBit write i l) (repeatBit read (n-i) r)
  have described : 𝚺ᴬ₁-Function₁ path := by
    unfold path encode
    definability
  have advance (i : M) (before : i < n) :
      tick m.workingStates m.packedRows (path i) = path (i+1) := by
    dsimp only [path]
    rw [remaining_step before,repeatBit_succ,Reaches.tick_of_row (dir := true) active row,repeatBit_succ]
    rfl
  simpa only [path,repeatBit_zero,Arithmetic.sub_zero,Arithmetic.sub_self] using
    clock_follows m n path described advance n (le_refl n)

theorem scan_left {m : Machine} {q : Nat} {read write : Bool}
    (active : q < m.workingStates) (row : m.row q read.toNat = 4*q+2*write.toNat)
    (n l r : M) :
    clock m.workingStates m.packedRows n (fromLeft q (repeatBit read n l) r) =
      fromLeft q l (repeatBit write n r) := by
  let path (i : M) := fromLeft q (repeatBit read (n-i) l) (repeatBit write i r)
  have described : 𝚺ᴬ₁-Function₁ path := by
    unfold path fromLeft encode divIn remIn
    definability
  have advance (i : M) (before : i < n) :
      tick m.workingStates m.packedRows (path i) = path (i+1) := by
    dsimp only [path]
    have edge : m.row q read.toNat = 4*q+2*write.toNat+false.toNat := by simpa using row
    rw [remaining_step before,repeatBit_succ,fromLeft_pushBit,
      Reaches.tick_of_row (dir := false) active edge,repeatBit_succ]
    rfl
  simpa only [path,repeatBit_zero,Arithmetic.sub_zero,Arithmetic.sub_self] using
    clock_follows m n path described advance n (le_refl n)

end PalomarI3380.ArithmeticMachine
