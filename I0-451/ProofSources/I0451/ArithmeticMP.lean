module
public import I0451.ArithmeticNip
public import I0451.ArithmeticStack
public import I0451.ModusPonens

/-! Model-valued formula construction and literal modus ponens. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelSaveOperand (s : Fin 9 → V) : Fin 9 → V :=
  putRegister (modelPushResult s) topWff (s parameterOne)

theorem model_save_operand (s : Fin 9 → V) (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    ModelEffect (.branch saveOperandEntry) s .normal (modelSaveOperand s) := by
  let pushed := modelPushResult s
  let copied := putRegister (modelAddAt (fun j => j == scratchOne || j == topWff)
    (pushed parameterOne) pushed) parameterOne 0
  have copy : ModelEffect (.branch ⟨115,false,true⟩) pushed .normal copied :=
    ModelEffect.while_add (block := ⟨127,true,false⟩) (body := .branch ⟨140,false,true⟩)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun j => j == scratchOne || j == topWff) (by decide)
      (fun v => ModelEffect.increment_two (by decide) (by decide +kernel) (by decide +kernel) v) pushed
  have restore := ModelEffect.move_one (root := ⟨33,true,true⟩) (block := ⟨48,true,true⟩)
    (source := scratchOne) (target := parameterOne) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) copied
  have ran := ModelEffect.sequence (root := saveOperandEntry) (by decide +kernel) (by decide +kernel)
    (model_stack_push s oneZero twoZero)
    (ModelEffect.sequence (root := ⟨109,true,false⟩) (by decide +kernel) (by decide +kernel) copy restore)
  have eq : modelTransfer scratchOne parameterOne copied = modelSaveOperand s := by
    funext j
    have one : s 6 = 0 := oneZero
    rcases index_cases j with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [copied, pushed, modelTransfer, modelAddAt, putRegister, modelSaveOperand, modelPushResult,
        nextProof, topWff, wffStack, axiomIndex, parameterOne, parameterTwo,
        scratchOne, scratchTwo, proofList, one]
  rwa [eq] at ran

noncomputable def modelImp (a b : V) : V := 4 * cantor a b

noncomputable def modelImplicationResult (s : Fin 9 → V) : Fin 9 → V :=
  putRegister (putRegister s wffStack (cantorRight (s wffStack))) topWff
    (modelImp (cantorLeft (s wffStack)) (s topWff))

private theorem model_multiply_four (s : Fin 9 → V) :
    ModelEffect (.branch ⟨131,true,true⟩) s .normal
      (putRegister (modelAddAt (· == topWff) (4 * s scratchTwo) s) scratchTwo 0) := by
  apply ModelEffect.while_add_scaled (block := ⟨144,true,true⟩) (body := .branch ⟨151,false,true⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (· == topWff) (by decide) 4 _ s
  intro t
  let bump (v : Fin 9 → V) := putRegister v topWff (v topWff + 1)
  have two (v : Fin 9 → V) : ModelEffect (.branch ⟨117,false,false⟩) v .normal (bump (bump v)) :=
    ModelEffect.sequence (by decide +kernel) (by decide +kernel) (.inc _ v) (.inc _ _)
  have more := (two (bump (bump t))).share (target := .branch ⟨117,true,false⟩)
    (sameProgram_sound (fuel := 2) (by decide +kernel))
  have four := ModelEffect.sequence (root := ⟨151,false,true⟩)
    (by decide +kernel) (by decide +kernel) (two t) more
  have eq : bump (bump (bump (bump t))) = modelAddAt (· == topWff) 4 t := by
    have numeral : (1 : V) + (1 + (1 + 1)) = 4 := by
      norm_num
    funext j
    by_cases top : j = topWff <;> simp [bump, modelAddAt, putRegister, top, add_assoc, numeral]
  rwa [eq] at four

theorem model_build_imp (s : Fin 9 → V) (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    ModelEffect (.branch buildImpEntry) s .normal (modelImplicationResult s) := by
  let unpacked := writeUnpaired (putRegister s wffStack 0) (s wffStack)
  let kept := modelTransfer scratchTwo wffStack unpacked
  let paired := modelPaired scratchOne topWff scratchTwo kept
  have unpack := model_unpair (entry := ⟨128,false,false⟩) (loop := ⟨44,true,false⟩)
    (source := wffStack) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide) s
  simp only [oneZero, twoZero, cantor_zero, zero_add] at unpack
  have keep := ModelEffect.move_one (root := ⟨129,true,false⟩) (block := ⟨141,true,true⟩)
    (source := scratchTwo) (target := wffStack) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) unpacked
  have pairRun := (model_stack_pair kept).share (target := .branch ⟨130,false,true⟩)
    (sameProgram_sound (fuel := 8) (by decide +kernel))
  have calculate := ModelEffect.sequence (root := ⟨119,true,true⟩)
    (by decide +kernel) (by decide +kernel) pairRun (model_multiply_four paired)
  have ran := ModelEffect.sequence (root := buildImpEntry) (by decide +kernel) (by decide +kernel)
    (ModelEffect.sequence (root := ⟨118,false,true⟩) (by decide +kernel) (by decide +kernel) unpack keep) calculate
  have eq : putRegister (modelAddAt (· == topWff) (4 * paired scratchTwo) paired) scratchTwo 0 =
      modelImplicationResult s := by
    funext j
    have one : s 6 = 0 := oneZero
    have two : s 7 = 0 := twoZero
    rcases index_cases j with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [unpacked, kept, paired, modelTransfer, modelPaired, modelAddAt, writeUnpaired,
        modelImplicationResult, modelImp, putRegister, nextProof, topWff, wffStack, axiomIndex, parameterOne, parameterTwo,
        scratchOne, scratchTwo, proofList, one, two]
  rwa [eq] at ran

noncomputable def modelMPResult (s : Fin 9 → V) : Fin 9 → V :=
  let cleared := putRegister (putRegister s topWff 0) parameterTwo 0
  if s parameterTwo = modelImp (s topWff) (s parameterOne) then modelSaveOperand cleared else cleared

theorem model_mp (s : Fin 9 → V) (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    ModelEffect (.branch mpCursor) s .normal (modelMPResult s) := by
  let pushed := modelSaveOperand s
  let formed := modelImplicationResult pushed
  let loaded := modelTransfer topWff scratchOne formed
  let cleared := putRegister (putRegister s topWff 0) parameterTwo 0
  have formedEq : formed = putRegister s topWff (modelImp (s topWff) (s parameterOne)) := by
    funext j
    by_cases ht : j = topWff
    · subst j
      simp [formed, pushed, modelSaveOperand, modelImplicationResult, modelPushResult, putRegister, topWff, wffStack]
    · by_cases hw : j = wffStack
      · subst j
        simp [formed, pushed, modelSaveOperand, modelImplicationResult, modelPushResult, putRegister, topWff, wffStack]
      · simp [formed, pushed, modelSaveOperand, modelImplicationResult, modelPushResult, putRegister, ht, hw]
  have fs : pushed scratchOne = 0 := by
    simpa [pushed, modelSaveOperand, modelPushResult, putRegister, scratchOne, topWff, wffStack] using oneZero
  have ss : pushed scratchTwo = 0 := by
    simpa [pushed, modelSaveOperand, modelPushResult, putRegister, scratchTwo, topWff, wffStack] using twoZero
  have build := ModelEffect.sequence (root := ⟨51,false,true⟩) (by decide +kernel) (by decide +kernel)
    (model_save_operand s oneZero twoZero) (model_build_imp pushed fs ss)
  have load := ModelEffect.move_one (root := ⟨69,false,true⟩) (block := ⟨89,true,false⟩)
    (source := topWff) (target := scratchOne) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) formed
  have tested := (model_compare_cache_gate loaded).share (target := .branch ⟨90,false,true⟩)
    (sameProgram_sound (fuel := 8) (by decide +kernel))
  have count : loaded scratchOne = modelImp (s topWff) (s parameterOne) := by
    simp [loaded, formedEq, modelTransfer, modelAddAt, putRegister, scratchOne, topWff,
      show s 6 = 0 from oneZero]
  have cached : loaded parameterTwo = s parameterTwo := by
    simp [loaded, formedEq, modelTransfer, modelAddAt, putRegister, parameterTwo, scratchOne, topWff]
  have clearEq : clearPair scratchOne parameterTwo loaded = cleared := by
    funext j
    have one : s 6 = 0 := oneZero
    rcases index_cases j with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [cleared, loaded, formedEq, clearPair, modelTransfer, modelAddAt, putRegister,
        nextProof, topWff, wffStack, axiomIndex, parameterOne, parameterTwo,
        scratchOne, scratchTwo, proofList, one]
  rw [count, cached, clearEq] at tested
  have handled : ModelEffect (.branch ⟨70,true,true⟩) loaded .normal (modelMPResult s) := by
    by_cases eq : s parameterTwo = modelImp (s topWff) (s parameterOne)
    · rw [ite_eq_left eq.symm] at tested
      simp only [modelMPResult, ite_eq_left eq]
      have saved := model_save_operand cleared
        (by simpa [cleared, putRegister, topWff, parameterTwo, scratchOne] using oneZero)
        (by simpa [cleared, putRegister, topWff, parameterTwo, scratchTwo] using twoZero)
      exact ModelEffect.sequence (by decide +kernel) (by decide +kernel) tested
        (saved.share (target := .branch ⟨91,true,true⟩)
          (sameProgram_sound (fuel := 8) (by decide +kernel)))
    · rw [ite_eq_right (Ne.symm eq)] at tested
      simpa only [modelMPResult, ite_eq_right eq] using
        (ModelEffect.leftExit (cursor := ⟨70,true,true⟩) (by decide +kernel) tested
          (show (Signal.break 0).leftExit = some .normal from rfl))
  exact ModelEffect.sequence (by decide +kernel) (by decide +kernel) build
    (ModelEffect.sequence (root := ⟨52,true,true⟩) (by decide +kernel) (by decide +kernel) load handled)

end I0451.Arithmetization
