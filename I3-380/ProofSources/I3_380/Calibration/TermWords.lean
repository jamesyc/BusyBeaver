module
public import I3_380.Calibration.FilterCoding
public import I3_380.Search.Arithmetic.WordEmission
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticMachine.SourceWords

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Use the finite filter language's function indices as the exact native
tags. A variable is interpreted at the distinguished ground constant D. -/
def termBlueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “out index. ∃ token, !pairDef token 0 1 ∧ !adjoinDef out token 0”
  fvar := .mkSigma “out index. ∃ token, !pairDef token 0 1 ∧ !adjoinDef out token 0”
  func := .mkSigma “out arity tag children mapped. ∃ token stack,
    !pairDef token arity tag ∧ !flattenBlueprint.resultDef stack mapped ∧ !adjoinDef out token stack”

noncomputable def termConstruction : Language.TermRec.Construction M termBlueprint where
  bvar _ _ := (⟪0,1⟫ : M) ∷ 0
  fvar _ _ := (⟪0,1⟫ : M) ∷ 0
  func _ arity tag _ mapped := ⟪arity,tag⟫ ∷ flattenTokens mapped
  bvar_defined := .mk fun v => by simp [termBlueprint]
  fvar_defined := .mk fun v => by simp [termBlueprint]
  func_defined := .mk fun v => by
    simp [termBlueprint,flattenTokens,(flattenConstruction.result_defined (V := M)).iff,Matrix.empty_eq]

noncomputable def termTokens (code : M) : M :=
  termConstruction.result FilterLanguage ![] code

noncomputable def termWord (code : M) : M :=
  emitVector (termTokens code) 0

noncomputable def termTokensDef : 𝚺ᴬ₁.Semisentence 2 :=
  termBlueprint.result FilterLanguage

instance termTokens_defined : 𝚺ᴬ₁-Function₁ (termTokens (M := M)) via termTokensDef :=
  .mk fun v => by
    simpa only [termTokensDef,termTokens,Matrix.empty_eq] using
      (termConstruction.result_defined (L := FilterLanguage) (V := M)).df v

@[definability] instance termTokens_definable : 𝚺ᴬ₁-Function₁ (termTokens (M := M)) :=
  termTokens_defined.to_definable

@[definability] instance termWord_definable : 𝚺ᴬ₁-Function₁ (termWord (M := M)) := by
  unfold termWord
  definability

end PalomarI3380.Calibration.TermWords
