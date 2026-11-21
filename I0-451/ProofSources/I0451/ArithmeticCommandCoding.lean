module
public import I0451.ArithmeticCandidates
public import I0451.ArithmeticValueDefinability

/-! A numeric coding of command boundaries and their transitions.
Zero records a halt. A successor stores the six live registers of a
normally returning command. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def packBoundary (s : Fin 9 → V) : V :=
  ⟪s nextProof, s topWff, s wffStack, s parameterOne, s parameterTwo, s proofList⟫ + 1

noncomputable def unpackBoundary (code : V) : Fin 9 → V :=
  let values := code - 1
  boundaryRegisters (π₁ values) (π₁ (π₂ values)) (π₁ (π₂ (π₂ values)))
    (π₁ (π₂ (π₂ (π₂ values)))) (π₁ (π₂ (π₂ (π₂ (π₂ values))))) (π₂ (π₂ (π₂ (π₂ (π₂ values)))))

theorem unpack_packBoundary {s : Fin 9 → V} (ready : CommandReady s) :
    unpackBoundary (packBoundary s) = s := by
  simpa only [unpackBoundary, packBoundary, add_tsub_cancel_right, pi₁_pair, pi₂_pair]
    using ready.boundaryRegisters

@[simp] theorem packBoundary_nonzero (s : Fin 9 → V) : packBoundary s ≠ 0 := by
  simp [packBoundary]

theorem packBoundary_definable {k : Nat} (s : (Fin k → V) → Fin 9 → V)
    (defS : ∀ i, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => s v i)) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => packBoundary (s v)) := by
  have a := defS nextProof
  have b := defS topWff
  have c := defS wffStack
  have d := defS parameterOne
  have e := defS parameterTwo
  have f := defS proofList
  unfold packBoundary
  definability

theorem unpackBoundary_field_defined (i : Fin 9) :
    𝚺ᴬ₁-Function₁[V] (fun code => unpackBoundary code i) := by
  rcases index_cases i with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    dsimp [unpackBoundary, boundaryRegisters, nextProof, topWff, wffStack, axiomIndex,
      parameterOne, parameterTwo, scratchOne, scratchTwo, proofList] <;> definability

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private theorem putRegister_defined {k : Nat} (s : (Fin k → V) → Fin 9 → V) (r i : Fin 9)
    (f : (Fin k → V) → V)
    (defS : ∀ j, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => s v j))
    (defF : 𝚺ᴬ₁.DefinableFunction (V := V) f) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => putRegister (s v) r (f v) i) := by
  by_cases same : i = r
  · simpa only [putRegister, same, ite_true] using defF
  · simpa only [putRegister, same, ite_false] using defS i

private theorem applyOperation_field_defined {k : Nat} (op : Operation)
    (s : (Fin k → V) → Fin 9 → V) (i : Fin 9)
    (ds : ∀ j, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => s v j)) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => op.modelApply (s v) i) := by
  have input (v : Fin k → V) : (symbolicInput false).modelEval (s v) = s v := by
    funext j
    simp [symbolicInput, SymbolicRegisters.modelEval, CounterExpr.modelEval]
  have output (v : Fin k → V) :
      (op.symbolic (symbolicInput false) i).modelEval (s v) = op.modelApply (s v) i := by
    have eq := op.modelEval_symbolic (symbolicInput false) (s v)
    rw [input v] at eq
    exact congrFun eq i
  simpa only [output] using counterExpr_modelEval_defined (op.symbolic (symbolicInput false) i) s ds

private theorem mpResult_field_defined {k : Nat} (s : (Fin k → V) → Fin 9 → V) (i : Fin 9)
    (ds : ∀ j, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => s v j)) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => modelMPResult (s v) i) := by
  let cleared := fun v => putRegister (putRegister (s v) topWff 0) parameterTwo 0
  have defCleared (j : Fin 9) : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => cleared v j) :=
    putRegister_defined _ _ _ _ (fun j => putRegister_defined _ _ j _ ds (by definability)) (by definability)
  have imp : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => modelImp (s v topWff) (s v parameterOne)) := by
    have t := ds topWff
    have a := ds parameterOne
    unfold modelImp
    definability
  have result := arithmeticCompare_defined (fun v => s v parameterTwo)
    (fun v => modelImp (s v topWff) (s v parameterOne))
    (fun v => Operation.saveOne.modelApply (cleared v) i) (fun v => cleared v i)
    (ds _) imp (applyOperation_field_defined .saveOne cleared i defCleared) (defCleared i)
  simpa only [modelMPResult, ite_apply, Operation.modelApply, cleared] using result

private theorem modelNip_field_defined {k : Nat} (s : (Fin k → V) → Fin 9 → V) (i : Fin 9)
    (ds : ∀ j, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => s v j)) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => modelNipResult (s v) i) := by
  have x := ds wffStack
  have fromStack : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => cantorLeft (s v wffStack)) := by definability
  have remain : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => cantorRight (s v wffStack)) := by definability
  exact (putRegister_defined
    (fun v => putRegister (putRegister (s v) parameterTwo 0) wffStack (cantorRight (s v wffStack)))
    parameterTwo i _ (fun j => putRegister_defined _ _ j _ (fun j' =>
      putRegister_defined _ _ j' _ ds (by definability)) remain) fromStack).of_eq _
      (by
        intro v
        let cleared := putRegister (s v) parameterTwo 0
        have stack : cleared wffStack = s v wffStack := putRegister_other _ (by decide) _
        have cache : cleared parameterTwo = 0 := putRegister_at _ _ _
        simp only [modelNipResult, modelReadFrom]
        change _ = putRegister (putRegister cleared wffStack (cantorRight (cleared wffStack)))
          parameterTwo (cleared parameterTwo + cantorLeft (cleared wffStack)) i
        rw [stack, cache, zero_add])

private theorem modelExtra_field_defined {k : Nat} (s : (Fin k → V) → Fin 9 → V) (i : Fin 9)
    (ds : ∀ j, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => s v j)) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => modelExtraResult (s v) i) := by
  have t := ds topWff
  have w := ds wffStack
  have saved : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v =>
      cantor (literalFoundationCode : V) (cantor (s v topWff) (s v wffStack))) := by definability
  unfold modelExtraResult
  apply putRegister_defined
  · intro j
    apply putRegister_defined
    · intro j'
      apply putRegister_defined
      · intro j''
        apply putRegister_defined
        · intro j'''
          exact putRegister_defined _ _ j''' _ ds (by definability)
        · exact saved
      · definability
    · definability
  · definability

private theorem modelPayload_defined {k : Nat} (s : (Fin k → V) → Fin 9 → V)
    (ds : ∀ j, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => s v j)) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => modelPayload (s v)) := by
  have queue := ds proofList
  exact arithmeticCompare_defined (fun v => s v proofList) (fun _ => 0)
    (fun v => s v nextProof) (fun v => s v proofList - 1)
    queue (by definability) (ds _) (by definability)

private theorem modelCommandInput_field_defined {k : Nat} (s : (Fin k → V) → Fin 9 → V) (i : Fin 9)
    (ds : ∀ j, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => s v j)) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => modelCommandInput (s v) i) := by
  have number := ds nextProof
  have next : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => modelNextIndex (s v)) :=
    arithmeticCompare_defined (fun v => s v proofList) (fun _ => 0)
      (fun v => s v nextProof + 1) (fun v => s v nextProof)
      (ds _) (by definability) (by definability) number
  have payload := modelPayload_defined s ds
  have operand := ds parameterOne
  unfold modelCommandInput
  apply putRegister_defined
  · intro j
    apply putRegister_defined
    · exact fun j => putRegister_defined _ _ j _ ds next
    · definability
  · definability

noncomputable def codeOfResult (result : Option (Fin 9 → V)) : V :=
  (result.map packBoundary).getD 0

theorem codeOfResult_zero_iff (result : Option (Fin 9 → V)) : codeOfResult result = 0 ↔ result = none := by
  cases result <;> simp [codeOfResult]

theorem codeOfResult_some (s : Fin 9 → V) : codeOfResult (some s) = packBoundary s := rfl

private theorem codeOfResult_ite (test : Prop) [Decidable test]
    (a b : Option (Fin 9 → V)) :
    codeOfResult (if test then a else b) = if test then codeOfResult a else codeOfResult b := by
  by_cases h : test <;> simp [h]

private theorem codeOfCommand_defined {k : Nat} (selector : (Fin k → V) → V)
    (s : (Fin k → V) → Fin 9 → V) (ds : ∀ j, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => s v j))
    (mode : 𝚺ᴬ₁.DefinableFunction (V := V) selector) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => codeOfResult (modelCommandResult (selector v) (s v))) := by
  let axInput (v : Fin k → V) := putRegister (s v) axiomIndex (selector v - 4)
  have axDefined (j : Fin 9) : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => axInput v j) :=
    putRegister_defined _ _ _ _ ds (by definability)
  have ax := packBoundary_definable (fun v => modelAxiomResult (axInput v))
    (fun i => modelAxiom_field_defined axInput i axDefined)
  have extra := packBoundary_definable (fun v => modelExtraResult (s v))
    (fun i => modelExtra_field_defined s i ds)
  have nip := packBoundary_definable (fun v => modelNipResult (s v))
    (fun i => modelNip_field_defined s i ds)
  have drop : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => packBoundary (modelDropResult (s v))) :=
    packBoundary_definable (fun v => modelDropResult (s v))
      (fun i => applyOperation_field_defined .saveTwo s i ds)
  have mp := packBoundary_definable (fun v => modelMPResult (s v))
    (fun i => mpResult_field_defined s i ds)
  simp only [modelCommandResult, codeOfResult_ite, codeOfResult_some]
  apply arithmeticCompare_defined _ _ _ _ mode (by definability) mp
  apply arithmeticCompare_defined _ _ _ _ mode (by definability) drop
  apply arithmeticCompare_defined _ _ _ _ mode (by definability)
  · apply arithmeticCompare_defined _ _ _ _ (ds _) (by definability) _ nip
    exact Bounding.HierarchySymbol.DefinableFunction.const 0
  · exact arithmeticCompare_defined _ _ _ _ mode (by definability) extra ax

theorem codeOfCommandStep_defined {k : Nat} (s : (Fin k → V) → Fin 9 → V)
    (ds : ∀ j, 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => s v j)) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => codeOfResult (modelCommandStep (s v))) := by
  have payload := modelPayload_defined s ds
  exact codeOfCommand_defined (fun v => cantorLeft (modelPayload (s v))) (fun v => modelCommandInput (s v))
    (fun i => modelCommandInput_field_defined s i ds) (by definability)

noncomputable def boundaryCodeStep (x : V) : V :=
  if x = 0 then 0 else codeOfResult (modelCommandStep (unpackBoundary x))

theorem boundaryCodeStep_defined :
    𝚺ᴬ₁-Function₁[V] (boundaryCodeStep : V → V) := by
  exact arithmeticCompare_defined (fun v : Fin 1 → V => v 0) (fun _ => 0)
    (fun _ => 0) (fun v => codeOfResult (modelCommandStep (unpackBoundary (v 0))))
    (by definability) (by definability) (by definability)
    (codeOfCommandStep_defined _ unpackBoundary_field_defined)

theorem boundaryCodeStep_pack {s : Fin 9 → V} (ready : CommandReady s) :
    boundaryCodeStep (packBoundary s) = codeOfResult (modelCommandStep s) := by
  simp [boundaryCodeStep, unpack_packBoundary ready]

end I0451.Arithmetization
