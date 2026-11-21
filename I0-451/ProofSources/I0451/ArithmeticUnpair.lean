module
public import I0451.ArithmeticLoops
public import I0451.ArithmeticCantor
public import I0451.OperandReading

/-! The actual unpacking loop follows the Cantor diagonals even when
its argument and its two scratch registers contain nonstandard values. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem scratch_ne : scratchOne ≠ scratchTwo := by decide

noncomputable def writeUnpaired (s : Fin 9 → V) (code : V) : Fin 9 → V :=
  putRegister (putRegister s scratchOne (cantorLeft code)) scratchTwo (cantorRight code)

private theorem advance_scratch (s : Fin 9 → V) :
    ModelEffect (.branch unpairBody) s .normal
      (writeUnpaired s (cantor (s scratchOne) (s scratchTwo) + 1)) := by
  let incremented := putRegister s scratchTwo (s scratchTwo + 1)
  let shifted := modelTransfer scratchTwo scratchOne incremented
  have shift : ModelEffect (.branch shiftCursor) incremented .normal shifted :=
    ModelEffect.move_one (block := shiftLoop) scratch_ne
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) incremented
  have tested : ModelEffect (.branch unpairTest) incremented .normal
      (if incremented scratchOne = 0 then shifted
        else putRegister incremented scratchOne (incremented scratchOne - 1)) :=
    ModelEffect.if_zero (test := unpairGuard) (body := .branch shiftCursor)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun _ => shift)
  have actual := ModelEffect.sequence (root := unpairBody) (by decide +kernel) (by decide +kernel)
    (ModelEffect.inc scratchTwo s) tested
  have sameOne : incremented scratchOne = s scratchOne := putRegister_other _ scratch_ne _
  rw [sameOne] at actual
  by_cases zero : s scratchOne = 0
  · rw [ite_eq_left zero] at actual
    have code : cantor (s scratchOne) (s scratchTwo) + 1 = cantor (s scratchTwo + 1) 0 := by
      rw [zero, cantor_wrap]
    rw [code]
    have result : shifted = writeUnpaired s (cantor (s scratchTwo + 1) 0) := by
      funext i
      by_cases first : i = scratchOne
      · subst i
        simp [shifted, incremented, modelTransfer, modelAddAt, writeUnpaired, putRegister, scratch_ne, zero]
      · by_cases second : i = scratchTwo <;>
          simp [shifted, incremented, modelTransfer, modelAddAt, writeUnpaired, putRegister, first, second]
    exact result ▸ actual
  · obtain ⟨n, positive⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr zero)
    rw [ite_eq_right zero, positive, add_tsub_cancel_right] at actual
    have code : cantor (s scratchOne) (s scratchTwo) + 1 = cantor n (s scratchTwo + 1) := by
      rw [positive, cantor_next]
    rw [code]
    have result : putRegister incremented scratchOne n = writeUnpaired s (cantor n (s scratchTwo + 1)) := by
      funext i
      by_cases first : i = scratchOne
      · subst i
        simp [incremented, writeUnpaired, putRegister, scratch_ne]
      · by_cases second : i = scratchTwo <;>
          simp [incremented, writeUnpaired, putRegister, first, second, Ne.symm scratch_ne]
    exact result ▸ actual

/-- The counter register is consumed, while the scratch registers
become the two projections of their initial Cantor code plus that counter. -/
theorem model_unpair {entry loop : Cursor} {source : Fin 9}
    (dec : outgoing entry false = some (.instruction (.dec source)))
    (body : outgoing entry true = some (.branch loop))
    (advance : outgoing loop false = some (.branch unpairBody))
    (repeatLoop : outgoing loop true = some (.instruction (.restart 1)))
    (first : source ≠ scratchOne) (second : source ≠ scratchTwo) (s : Fin 9 → V) :
    ModelEffect (.branch entry) s .normal
      (writeUnpaired (putRegister s source 0) (cantor (s scratchOne) (s scratchTwo) + s source)) := by
  let code := cantor (s scratchOne) (s scratchTwo)
  let atClock (j : V) := writeUnpaired (putRegister s source (s source - j)) (code + j)
  have start : atClock 0 = s := by
    funext i
    by_cases one : i = scratchOne
    · subst i
      simp [atClock, writeUnpaired, putRegister, code, scratch_ne]
    · by_cases two : i = scratchTwo
      · subst i
        simp [atClock, writeUnpaired, code]
      · by_cases sourceIndex : i = source <;>
          simp [atClock, writeUnpaired, putRegister, one, two, sourceIndex, first, second]
  have source_eq (j : V) : atClock j source = s source - j := by
    simp [atClock, writeUnpaired, putRegister, first, second]
  have defined (i : Fin 9) : 𝚺ᴬ₁-Function₁[V] (fun j => atClock j i) := by
    by_cases one : i = scratchOne <;> by_cases two : i = scratchTwo <;> by_cases src : i = source <;>
      simp only [atClock, writeUnpaired, putRegister, one, two, src, ite_true, ite_false, code] <;> definability
  have each (j : V) :
      ModelEffect (.branch unpairBody)
        (putRegister (atClock j) source (s source - (j + 1))) .normal (atClock (j + 1)) := by
    let deced := putRegister (atClock j) source (s source - (j + 1))
    have firstComponent : deced scratchOne = cantorLeft (code + j) := by
      simp [deced, atClock, writeUnpaired, putRegister, Ne.symm first, scratch_ne]
    have secondComponent : deced scratchTwo = cantorRight (code + j) := by
      simp [deced, atClock, writeUnpaired, putRegister, Ne.symm second]
    have pairEq : cantor (deced scratchOne) (deced scratchTwo) = code + j := by
      rw [firstComponent, secondComponent]
      exact cantor_encode_decode _
    have step := advance_scratch deced
    rw [pairEq, add_assoc] at step
    have result : writeUnpaired deced (code + (j + 1)) = atClock (j + 1) := by
      funext i
      by_cases one : i = scratchOne
      · simp [one, atClock, writeUnpaired, putRegister]
      · by_cases two : i = scratchTwo
        · simp [two, atClock, writeUnpaired, putRegister]
        · by_cases sourceIndex : i = source <;>
            simp [atClock, deced, writeUnpaired, putRegister, one, two, sourceIndex]
    exact result ▸ step
  have all := ModelEffect.while_count dec body advance repeatLoop atClock (s source) defined source_eq
    (fun j _ => each j)
  rw [start] at all
  simpa only [atClock, Arithmetic.sub_self, code] using all

theorem model_unpair_prooflist (s : Fin 9 → V) :
    ModelEffect (.branch unpairCursor) s .normal
      (writeUnpaired (putRegister s proofList 0) (cantor (s scratchOne) (s scratchTwo) + s proofList)) :=
  model_unpair (loop := unpairLoop) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) s

end I0451.Arithmetization
