module
public import I0451.ArithmeticLoops
public import I0451.ProofStackPop

/-! The literal NIP comparison, including iteration counts in arbitrary
arithmetic models. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ModelEffect.clear_counter {root : Cursor} {r : Fin 9}
    (dec : outgoing root false = some (.instruction (.dec r)))
    (back : outgoing root true = some (.instruction (.restart 0))) (s : Fin 9 → V) :
    ModelEffect (.branch root) s .normal (putRegister s r 0) := by
  let states (j : V) := putRegister s r (s r - j)
  have start : states 0 = s := by simp [states, putRegister_read]
  have done : states (s r) = putRegister s r 0 := by simp [states]
  have defined (i : Fin 9) : 𝚺ᴬ₁-Function₁[V] (fun j => states j i) := by
    by_cases eq : i = r <;> simp only [states, putRegister, eq, ite_true, ite_false] <;> definability
  have step (j : V) (lt : j < s r) :
      ModelEffect (.instruction (.dec r)) (states j) .normal (states (j + 1)) := by
    rw [show states (j + 1) = putRegister (states j) r (s r - (j + 1)) from
      (putRegister_overwrite _ _ _ _).symm]
    apply ModelEffect.dec_pos
    simpa [states] using (sub_succ_add_succ lt (0 : V)).symm
  have finish : ModelEffect (.branch root) (states (s r)) .normal (putRegister s r 0) := by
    rw [done]
    exact .leftExit dec (.dec_zero r _ (putRegister_at _ _ _)) rfl
  have ran := ModelEffect.repeat_until dec back states (s r) defined step
    (fun j _ => .restartLeaf 0 (states (j + 1))) finish
  rwa [start] at ran

noncomputable def modelCompareResult (x y : Fin 9) (s : Fin 9 → V) : Fin 9 → V :=
  putRegister (putRegister s x 0) y ((s x - s y) + (s y - s x))

/-- After the lesser number of iterations, the loop exits through its
zero test or moves the residual first operand into the second. -/
private theorem model_compare_loop {root afterFirst testSecond : Cursor} {mismatch : Edge} {x y : Fin 9}
    (distinct : x ≠ y)
    (readX : outgoing root false = some (.instruction (.dec x)))
    (testY : outgoing root true = some (.branch afterFirst))
    (enterY : outgoing afterFirst false = some (.branch testSecond))
    (enterMismatch : outgoing afterFirst true = some mismatch)
    (readY : outgoing testSecond false = some (.instruction (.dec y)))
    (reenter : outgoing testSecond true = some (.instruction (.restart 1)))
    (remainder : ∀ s : Fin 9 → V, s y = 0 →
      ModelEffect mismatch s .normal (putRegister (putRegister s x 0) y (s x + 1)))
    (s : Fin 9 → V) :
    ModelEffect (.branch root) s .normal (modelCompareResult x y s) := by
  let limit : V := min (s x) (s y)
  let states (j : V) := putRegister (putRegister s x (s x - j)) y (s y - j)
  let middle (j : V) := putRegister (states j) x (s x - (j + 1))
  have start : states 0 = s := by simp [states, putRegister_read]
  have defined (i : Fin 9) : 𝚺ᴬ₁-Function₁[V] (fun j => states j i) := by
    by_cases iy : i = y <;> by_cases ix : i = x <;>
      simp only [states, putRegister, iy, ix, ite_true, ite_false] <;> definability
  have xStep (j : V) (lt : j < s x) :
      ModelEffect (.instruction (.dec x)) (states j) .normal (middle j) := by
    apply ModelEffect.dec_pos
    simpa [states, putRegister, distinct] using (sub_succ_add_succ lt (0 : V)).symm
  have step (j : V) (lt : j < limit) :
      ModelEffect (.branch afterFirst) (middle j) (.restart 0) (states (j + 1)) := by
    have yy : middle j y = (s y - (j + 1)) + 1 := by
      simpa [middle, states, putRegister, Ne.symm distinct] using
        (sub_succ_add_succ (lt_of_lt_of_le lt (min_le_right (s x) (s y))) (0 : V)).symm
    have eq : putRegister (middle j) y (s y - (j + 1)) = states (j + 1) := by
      funext i
      by_cases iy : i = y <;> by_cases ix : i = x <;>
        simp [middle, states, putRegister, iy, ix]
    have dec := ModelEffect.dec_pos y (middle j) _ yy
    rw [eq] at dec
    have back : ModelEffect (.branch testSecond) (middle j) (.restart 0) (states (j + 1)) :=
      .rightExit readY reenter dec (.restartLeaf 1 _) rfl
    exact .leftExit enterY back rfl
  have finish : ModelEffect (.branch root) (states limit) .normal (modelCompareResult x y s) := by
    by_cases ordered : s x ≤ s y
    · have limitEq : limit = s x := min_eq_left ordered
      have zx : states limit x = 0 := by simp [states, limitEq, putRegister, distinct]
      have eq : states limit = modelCompareResult x y s := by
        simp [states, modelCompareResult, limitEq, sub_eq_zero_iff_le.mpr ordered]
      rw [← eq]
      exact .leftExit readX (.dec_zero x _ zx) rfl
    · have lt : s y < s x := lt_of_not_ge ordered
      have limitEq : limit = s y := min_eq_right (le_of_lt lt)
      have zy : middle limit y = 0 := by simp [middle, states, limitEq, putRegister, Ne.symm distinct]
      have residual : middle limit x + 1 = s x - s y := by
        simpa [middle, limitEq] using sub_succ_add_succ lt (0 : V)
      have eq : putRegister (putRegister (middle limit) x 0) y (middle limit x + 1) =
          modelCompareResult x y s := by
        rw [residual]
        funext i
        by_cases iy : i = y <;> by_cases ix : i = x <;>
          simp [middle, states, modelCompareResult, putRegister, iy, ix, sub_eq_zero_iff_le.mpr (le_of_lt lt)]
      have move := remainder (middle limit) zy
      rw [eq] at move
      have test : ModelEffect (.branch testSecond) (middle limit) .normal (middle limit) :=
        .leftExit readY (.dec_zero y _ zy) rfl
      exact .rightExit readX testY (xStep limit (limitEq ▸ lt))
        (ModelEffect.sequence enterY enterMismatch test move) rfl
  have ran := ModelEffect.repeat_until readX testY states limit defined
    (fun j lt => xStep j (lt_of_lt_of_le lt (min_le_left _ _))) step finish
  rwa [start] at ran

private theorem model_compare_cache (s : Fin 9 → V) :
    ModelEffect (.branch compareEntry) s .normal (modelCompareResult scratchOne parameterTwo s) := by
  apply model_compare_loop (afterFirst := ⟨120,true,false⟩) (testSecond := ⟨132,false,true⟩)
    (mismatch := .branch ⟨133,true,true⟩)
  · decide
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro regs empty
    let moved := modelTransfer scratchOne parameterTwo regs
    have move := ModelEffect.move_one (root := ⟨102,false,true⟩) (block := ⟨116,true,false⟩)
      (source := scratchOne) (target := parameterTwo) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) regs
    have ran := ModelEffect.sequence (root := ⟨133,true,true⟩)
      (by decide +kernel) (by decide +kernel) move (ModelEffect.inc parameterTwo moved)
    have count : moved parameterTwo = regs scratchOne := by
      simp [moved, modelTransfer, modelAddAt, putRegister, parameterTwo, scratchOne,
        show regs 5 = 0 from empty]
    have eq : putRegister moved parameterTwo (moved parameterTwo + 1) =
        putRegister (putRegister regs scratchOne 0) parameterTwo (regs scratchOne + 1) := by
      rw [count]
      funext i
      by_cases iy : i = parameterTwo <;> simp [moved, modelTransfer, modelAddAt, putRegister, iy]
    rwa [eq] at ran

private theorem model_test_cache (s : Fin 9 → V) :
    ModelEffect (.branch compareGuard) s
      (if s parameterTwo = 0 then .normal else .break 0) (putRegister s parameterTwo 0) := by
  by_cases zero : s parameterTwo = 0
  · rw [ite_eq_left zero, ← zero, putRegister_read]
    exact .leftExit (by decide +kernel) (.dec_zero parameterTwo _ zero) rfl
  · obtain ⟨n, pos⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr zero)
    rw [ite_eq_right zero]
    let reduced := putRegister s parameterTwo n
    have clear : ModelEffect (.branch ⟨134,false,true⟩) reduced .normal (putRegister reduced parameterTwo 0) :=
      ModelEffect.clear_counter (by decide +kernel) (by decide +kernel) reduced
    rw [show putRegister reduced parameterTwo 0 = putRegister s parameterTwo 0 from
      putRegister_overwrite _ _ _ _] at clear
    have skip : ModelEffect (.branch ⟨121,true,true⟩) reduced (.break 0) (putRegister s parameterTwo 0) :=
      .rightExit (by decide +kernel) (by decide +kernel) clear (.breakLeaf 0 _) rfl
    exact .rightExit (by decide +kernel) (by decide +kernel) (.dec_pos parameterTwo _ n pos) skip rfl

theorem model_compare_cache_gate (s : Fin 9 → V) :
    ModelEffect (.branch nipCompare) s
      (if s scratchOne = s parameterTwo then .normal else .break 0)
      (clearPair scratchOne parameterTwo s) := by
  let mid := modelCompareResult scratchOne parameterTwo s
  have tested := model_test_cache mid
  have zero_iff : mid parameterTwo = 0 ↔ s scratchOne = s parameterTwo := by
    rw [show mid parameterTwo = (s scratchOne - s parameterTwo) +
      (s parameterTwo - s scratchOne) from putRegister_at _ _ _]
    constructor
    · intro zero
      obtain ⟨left, right⟩ := eq_zero_of_eq_add_zero zero
      exact le_antisymm (sub_eq_zero_iff_le.mp left) (sub_eq_zero_iff_le.mp right)
    · intro same
      simp [same]
  have eq : putRegister mid parameterTwo 0 = clearPair scratchOne parameterTwo s := by
    simp [mid, modelCompareResult, clearPair, putRegister_overwrite]
  rw [eq] at tested
  simp only [zero_iff] at tested
  refine .rightExit (by decide +kernel) (by decide +kernel) (model_compare_cache s) tested ?_
  split <;> rfl

end I0451.Arithmetization
