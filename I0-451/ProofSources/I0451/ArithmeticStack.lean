module
public import I0451.ArithmeticPairing
public import I0451.ArithmeticInput
public import I0451.ProofStackPush
public import I0451.CommandInputs

/-! Literal stack construction and DROP with model-valued formula
codes and stack contents. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem fill_stack (s : Fin 9 → V) :
    ModelEffect (.branch fillEntry) s .normal (modelFillPair scratchOne topWff scratchTwo s) :=
  ModelEffect.while_add (block := fillLoop) (body := .branch fillBody)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun j => j == scratchOne || j == scratchTwo) (by decide)
    (fun v => ModelEffect.increment_two (by decide) (by decide +kernel) (by decide +kernel) v) s

private theorem rotate_stack (s : Fin 9 → V) :
    ModelEffect (.branch rotateEntry) s .normal (modelRotatePair scratchOne topWff scratchTwo s) := by
  have transfer := ModelEffect.move_one (root := ⟨162,true,false⟩) (block := ⟨152,true,true⟩)
    (source := scratchOne) (target := topWff) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (putRegister s scratchTwo (s scratchTwo + 1))
  exact ModelEffect.sequence (by decide +kernel) (by decide +kernel) (.inc scratchTwo s) transfer

theorem model_stack_pair (s : Fin 9 → V) :
    ModelEffect (.branch pairEntry) s .normal (modelPaired scratchOne topWff scratchTwo s) :=
  model_pair (test := pairTest) (cycle := pairRepeat) (fill := .branch fillEntry) (move := .branch rotateEntry)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) fill_stack rotate_stack s

noncomputable def modelPushResult (s : Fin 9 → V) : Fin 9 → V :=
  putRegister (putRegister s topWff 0) wffStack (cantor (s topWff) (s wffStack))

theorem model_stack_push (s : Fin 9 → V) (firstZero : s scratchOne = 0) (secondZero : s scratchTwo = 0) :
    ModelEffect (.branch stackPushCursor) s .normal (modelPushResult s) := by
  let a := modelTransfer topWff scratchOne s
  let b := modelTransfer wffStack topWff a
  let c := modelPaired scratchOne topWff scratchTwo b
  let d := modelTransfer scratchTwo wffStack c
  have first := ModelEffect.move_one (root := ⟨69,false,false⟩) (block := ⟨89,true,false⟩)
    (source := topWff) (target := scratchOne) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) s
  have second := ModelEffect.move_one (root := ⟨145,false,false⟩) (block := ⟨152,true,false⟩)
    (source := wffStack) (target := topWff) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a
  have third := model_stack_pair b
  have fourth := ModelEffect.move_one (root := ⟨129,true,true⟩) (block := ⟨141,true,true⟩)
    (source := scratchTwo) (target := wffStack) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) c
  have rest := ModelEffect.sequence (root := pushRest) (by decide +kernel) (by decide +kernel)
    (ModelEffect.sequence (root := pushPair) (by decide +kernel) (by decide +kernel) second third) fourth
  have ran : ModelEffect (.branch stackPushCursor) s .normal d :=
    ModelEffect.sequence (by decide +kernel) (by decide +kernel) first rest
  have same : d = modelPushResult s := by
    funext j
    have one : s 6 = 0 := firstZero
    have two : s 7 = 0 := secondZero
    rcases index_cases j with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [d, c, b, a, modelTransfer, modelPaired, modelAddAt, putRegister, modelPushResult,
        nextProof, topWff, wffStack, axiomIndex, parameterOne, parameterTwo, scratchOne, scratchTwo,
        proofList, one, two]
  rwa [same] at ran

noncomputable def modelDropResult (s : Fin 9 → V) : Fin 9 → V :=
  putRegister (modelPushResult s) topWff (s parameterTwo)

theorem model_drop (s : Fin 9 → V) (firstZero : s scratchOne = 0) (secondZero : s scratchTwo = 0) :
    ModelEffect (.branch dropCursor) s .normal (modelDropResult s) := by
  let pushed := modelPushResult s
  let copied := putRegister (modelAddAt (fun j => j == scratchOne || j == topWff)
    (pushed parameterTwo) pushed) parameterTwo 0
  let restored := modelTransfer scratchOne parameterTwo copied
  have copy : ModelEffect (.branch ⟨115,true,false⟩) pushed .normal copied :=
    ModelEffect.while_add (block := ⟨127,true,true⟩) (body := .branch ⟨140,false,true⟩)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun j => j == scratchOne || j == topWff) (by decide)
      (fun v => ModelEffect.increment_two (by decide) (by decide +kernel) (by decide +kernel) v) pushed
  have restore := ModelEffect.move_one (root := ⟨102,true,true⟩) (block := ⟨116,true,true⟩)
    (source := scratchOne) (target := parameterTwo) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) copied
  have ready := ModelEffect.sequence (root := ⟨101,false,true⟩) (by decide +kernel) (by decide +kernel)
    (model_stack_push s firstZero secondZero) copy
  have ran : ModelEffect (.branch dropCursor) s .normal restored :=
    ModelEffect.sequence (by decide +kernel) (by decide +kernel) ready restore
  have same : restored = modelDropResult s := by
    funext j
    have one : s 6 = 0 := firstZero
    rcases index_cases j with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [restored, copied, pushed, modelTransfer, modelAddAt, putRegister, modelDropResult,
        modelPushResult, nextProof, topWff, wffStack, axiomIndex, parameterOne, parameterTwo,
        scratchOne, scratchTwo, proofList, one]
  rwa [same] at ran

end I0451.Arithmetization
