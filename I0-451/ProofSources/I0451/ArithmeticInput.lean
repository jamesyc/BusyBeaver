module
public import I0451.ArithmeticUnpair

/-! The literal candidate loader and the two initial operand reads. -/

@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime _root_.I0451.Runtime.CandidateInput

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ModelEffect.increment_two {root : Cursor} {a b : Fin 9} (different : a ≠ b)
    (left : outgoing root false = some (.instruction (.inc a)))
    (right : outgoing root true = some (.instruction (.inc b))) (s : Fin 9 → V) :
    ModelEffect (.branch root) s .normal (modelAddAt (fun j => j == a || j == b) 1 s) := by
  have both : modelAddAt (· == b) 1 (modelAddAt (· == a) 1 s) =
      modelAddAt (fun j => j == a || j == b) 1 s := by
    funext i
    by_cases aHit : i = a
    · simp [modelAddAt, aHit, different]
    · by_cases bHit : i = b <;> simp [modelAddAt, aHit, bHit, Ne.symm different]
  rw [← both]
  exact ModelEffect.sequence left right (.increment_one a s) (.increment_one b _)

noncomputable def modelAfterLoad (s : Fin 9 → V) : Fin 9 → V :=
  if s proofList = 0 then
    putRegister (putRegister s proofList (s nextProof)) nextProof (s nextProof + 1)
  else putRegister s proofList (s proofList - 1)

private theorem load (s : Fin 9 → V) (empty : s proofList = 0) (clean : s scratchOne = 0) :
    ModelEffect (.branch loadCursor) s .normal
      (putRegister (putRegister s proofList (s nextProof)) nextProof (s nextProof + 1)) := by
  let selected : Fin 9 → Bool := fun j => j == proofList || j == scratchOne
  let copied := putRegister (modelAddAt selected (s nextProof) s) nextProof 0
  let restored := modelTransfer scratchOne nextProof copied
  have copy : ModelEffect (.branch copyCursor) s .normal copied :=
    ModelEffect.while_add (block := copyLoop) (body := .branch copyIncrements)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      selected (by decide)
      (fun v => ModelEffect.increment_two (by decide) (by decide +kernel) (by decide +kernel) v) s
  have restore : ModelEffect (.branch restoreCursor) copied .normal restored :=
    ModelEffect.move_one (block := CandidateInput.restoreLoop) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) copied
  have moved := ModelEffect.sequence (root := loadCursor) (by decide +kernel) (by decide +kernel) copy
    (ModelEffect.sequence (root := incrementCursor) (by decide +kernel) (by decide +kernel)
      restore (ModelEffect.inc nextProof restored))
  have result : putRegister restored nextProof (restored nextProof + 1) =
      putRegister (putRegister s proofList (s nextProof)) nextProof (s nextProof + 1) := by
    funext j
    have scratchNext : scratchOne ≠ nextProof := by decide
    have scratchList : scratchOne ≠ proofList := by decide
    have listNext : proofList ≠ nextProof := by decide
    by_cases q : j = nextProof
    · subst j
      simp [restored, copied, modelTransfer, modelAddAt, selected, putRegister, Ne.symm scratchNext, scratchNext, clean]
    · by_cases r : j = scratchOne
      · subst j
        simp [restored, modelTransfer, putRegister, scratchNext, scratchList, clean]
      · by_cases t : j = proofList
        · subst j
          simp [restored, copied, modelTransfer, modelAddAt, selected, putRegister, listNext, Ne.symm scratchList, empty]
        · simp [restored, copied, modelTransfer, modelAddAt, selected, putRegister, q, r, t]
  rwa [result] at moved

theorem model_candidate_loader (s : Fin 9 → V) (clean : s scratchOne = 0) :
    ModelEffect (.branch setupCursor) s .normal (modelAfterLoad s) := by
  unfold modelAfterLoad
  exact ModelEffect.if_zero (test := testCursor) (body := .branch loadCursor)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun empty => load s empty clean)

noncomputable def modelReadFrom (source target : Fin 9) (s : Fin 9 → V) : Fin 9 → V :=
  putRegister (putRegister s source (cantorRight (s source))) target
    (s target + cantorLeft (s source))

noncomputable def modelRead := modelReadFrom (V := V) proofList

theorem model_read_transfers {source target : Fin 9} (s : Fin 9 → V)
    (dl₁ : source ≠ scratchOne) (dl₂ : source ≠ scratchTwo)
    (targetOne : target ≠ scratchOne) (targetTwo : target ≠ scratchTwo)
    (targetList : target ≠ source) (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    modelTransfer scratchOne target
      (modelTransfer scratchTwo source (writeUnpaired (putRegister s source 0) (s source))) =
      modelReadFrom source target s := by
  let split := writeUnpaired (putRegister s source 0) (s source)
  let restored := modelTransfer scratchTwo source split
  change modelTransfer scratchOne target restored = _
  funext j
  have ds : scratchOne ≠ scratchTwo := by decide
  by_cases a : j = scratchOne
  · subst j
    simp [modelTransfer, modelReadFrom, putRegister, Ne.symm dl₁, Ne.symm targetOne, oneZero]
  · by_cases b : j = scratchTwo
    · subst j
      simp [modelTransfer, modelAddAt, modelReadFrom, putRegister, restored, a,
        Ne.symm dl₂, Ne.symm targetTwo, twoZero]
    · by_cases c : j = source
      · subst j
        simp [modelTransfer, modelAddAt, modelReadFrom, restored, split, writeUnpaired, putRegister,
          dl₁, dl₂, Ne.symm targetList]
      · by_cases d : j = target
        · subst j
          simp [modelTransfer, modelAddAt, modelReadFrom, restored, split, writeUnpaired, putRegister,
            ds, Ne.symm dl₁, targetOne, targetTwo, targetList]
        · simp [modelTransfer, modelAddAt, modelReadFrom, restored, split, writeUnpaired, putRegister, a, b, c, d]

private theorem read {start move : Cursor} {target : Fin 9}
    (left : outgoing start false = some (.branch unpackRestore))
    (right : outgoing start true = some (.branch move))
    (moveFirst : ∀ s : Fin 9 → V, ModelEffect (.branch move) s .normal
      (modelTransfer scratchOne target s))
    (targetOne : target ≠ scratchOne) (targetTwo : target ≠ scratchTwo)
    (targetList : target ≠ proofList) (s : Fin 9 → V)
    (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    ModelEffect (.branch start) s .normal (modelRead target s) := by
  let split := writeUnpaired (putRegister s proofList 0) (s proofList)
  let restored := modelTransfer scratchTwo proofList split
  have unpaired := model_unpair_prooflist s
  simp only [oneZero, twoZero, cantor_zero, zero_add] at unpaired
  have restore : ModelEffect (.branch restoreList) split .normal restored :=
    ModelEffect.move_one (block := Runtime.restoreLoop) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) split
  have prefixRun := ModelEffect.sequence (root := unpackRestore)
    (by decide +kernel) (by decide +kernel) unpaired restore
  have actual := ModelEffect.sequence left right prefixRun (moveFirst restored)
  have result : modelTransfer scratchOne target restored = modelRead target s :=
    model_read_transfers s (by decide) (by decide) targetOne targetTwo targetList oneZero twoZero
  rwa [result] at actual

theorem model_read_selector (s : Fin 9 → V) (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    ModelEffect (.branch readSelector) s .normal (modelRead axiomIndex s) := by
  refine read (move := ⟨19, true, false⟩) (by decide +kernel) (by decide +kernel)
    (fun state => ModelEffect.move_one (block := ⟨32,true,true⟩) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) state)
    (by decide) (by decide) (by decide) s oneZero twoZero

theorem model_read_operand (s : Fin 9 → V) (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    ModelEffect (.branch readOperand) s .normal (modelRead parameterOne s) := by
  refine read (move := ⟨33, true, false⟩) (by decide +kernel) (by decide +kernel)
    (fun state => ModelEffect.move_one (block := ⟨48,true,true⟩) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) state)
    (by decide) (by decide) (by decide) s oneZero twoZero

end I0451.Arithmetization
