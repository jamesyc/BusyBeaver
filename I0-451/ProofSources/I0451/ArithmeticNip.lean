module
public import I0451.ArithmeticCompare
public import I0451.ArithmeticInput

/-! Model arithmetic for the literal command that checks contradiction
and otherwise pops the cached proof. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem model_nip_halt (s : Fin 9 → V) (firstZero : s scratchOne = 0) (code : s parameterTwo = 1) :
    ModelEffect (.branch nipCursor) s .halt
      (clearPair scratchOne parameterTwo (putRegister s scratchOne 1)) := by
  let raised := putRegister s scratchOne (s scratchOne + 1)
  let cleared := clearPair scratchOne parameterTwo raised
  have same : raised scratchOne = raised parameterTwo := by
    simp [raised, putRegister, scratchOne, parameterTwo,
      show s 6 = 0 from firstZero, show s 5 = 1 from code]
  have ran := model_compare_cache_gate raised
  rw [ite_eq_left same] at ran
  have leaf : ModelEffect (.branch nipCondition) raised .halt cleared :=
    .rightExit (by decide +kernel) (by decide +kernel) ran (.haltLeaf cleared) rfl
  have test : ModelEffect (.branch nipRest) raised .halt cleared :=
    .leftExit (by decide +kernel) leaf rfl
  have head : ModelEffect (.branch nipHead) s .halt cleared :=
    .rightExit (by decide +kernel) (by decide +kernel) (.inc scratchOne s) test rfl
  simpa only [cleared, raised, firstZero, zero_add] using
    (ModelEffect.leftExit (cursor := nipCursor) (by decide +kernel) head rfl)

noncomputable def modelNipResult (s : Fin 9 → V) : Fin 9 → V :=
  modelReadFrom wffStack parameterTwo (putRegister s parameterTwo 0)

theorem model_nip (s : Fin 9 → V) (firstZero : s scratchOne = 0) (secondZero : s scratchTwo = 0)
    (safe : s parameterTwo ≠ 1) : ModelEffect (.branch nipCursor) s .normal (modelNipResult s) := by
  let raised := putRegister s scratchOne (s scratchOne + 1)
  let cleared := putRegister s parameterTwo 0
  have unequal : raised scratchOne ≠ raised parameterTwo := by
    simp [raised, putRegister, scratchOne, parameterTwo, show s 6 = 0 from firstZero,
      Ne.symm (show s 5 ≠ 1 from safe)]
  have test := model_compare_cache_gate raised
  rw [ite_eq_right unequal] at test
  have eq : clearPair scratchOne parameterTwo raised = cleared := by
    have cancel : putRegister s scratchOne 0 = s := by rw [← firstZero, putRegister_read]
    simp [clearPair, raised, cleared, putRegister_overwrite, cancel]
  rw [eq] at test
  have noHalt : ModelEffect (.branch nipCondition) raised .normal cleared :=
    .leftExit (by decide +kernel) test rfl
  have s₁ : cleared scratchOne = 0 := by
    rw [show cleared scratchOne = s scratchOne from putRegister_other _ (by decide) _]
    exact firstZero
  have s₂ : cleared scratchTwo = 0 := by
    rw [show cleared scratchTwo = s scratchTwo from putRegister_other _ (by decide) _]
    exact secondZero
  let split := writeUnpaired (putRegister cleared wffStack 0) (cleared wffStack)
  let stored := modelTransfer scratchTwo wffStack split
  have prepare := model_unpair (entry := ⟨128,false,true⟩) (loop := ⟨44,true,false⟩)
    (source := wffStack) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) cleared
  simp only [s₁, s₂, cantor_zero, zero_add] at prepare
  have append := ModelEffect.move_one (root := ⟨129,true,true⟩) (block := ⟨141,true,true⟩)
    (source := scratchTwo) (target := wffStack) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) split
  have pop := ModelEffect.sequence (root := popEntry) (by decide +kernel) (by decide +kernel) prepare append
  have read := ModelEffect.sequence (root := nipRest) (by decide +kernel) (by decide +kernel) noHalt pop
  have head := ModelEffect.sequence (root := nipHead) (by decide +kernel) (by decide +kernel)
    (ModelEffect.inc scratchOne s) read
  have final := ModelEffect.move_one (root := ⟨102,true,true⟩) (block := ⟨116,true,true⟩)
    (source := scratchOne) (target := parameterTwo) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) stored
  have done := ModelEffect.sequence (root := nipCursor) (by decide +kernel) (by decide +kernel) head final
  have result := model_read_transfers (source := wffStack) (target := parameterTwo) cleared
    (by decide) (by decide) (by decide) (by decide) (by decide) s₁ s₂
  simpa only [stored, split, result, modelNipResult] using done

end I0451.Arithmetization
