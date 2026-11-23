module
public import I3_334Support.Search.Arithmetic.TokenConsumption
public import I3_334.Calibration.ModelScanTotal
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Arithmetic (Chain)
open ArithmeticMachine.SourceCantor
open ArithmeticMachine.SourceWords
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def rawCons (arity tag rest : M) : M := pairValue arity (pairValue tag rest)

noncomputable def rawConsDef : 𝚺ᴬ₁.Semisentence 4 :=
  .mkSigma “out arity tag rest. ∃ suffix,
    !ArithmeticMachine.SourceCantor.pairGraph suffix tag rest ∧
      !ArithmeticMachine.SourceCantor.pairGraph out arity suffix”

theorem rawConsDef_eval (out a t w : M) :
    rawConsDef.val.Evalb ![out,a,t,w] ↔ out = rawCons a t w := by
  simp [rawConsDef,rawCons,ArithmeticMachine.SourceCantor.pair_graph]

noncomputable def rawEmissionBlueprint : VecRec.Blueprint 2 where
  nil := .mkSigma “out suffix offset. out = suffix”
  adjoin := .mkSigma “out token rest previous suffix offset. ∃ a t b,
    !pairDef token a t ∧ !subDef b t offset ∧ !rawConsDef out a b previous”

noncomputable def rawEmissionConstruction : VecRec.Construction M rawEmissionBlueprint where
  nil args := args 0
  adjoin (args token _ previous) := rawCons (π₁ token) (π₂ token - args 1) previous
  nil_defined := .mk fun v => by simp [rawEmissionBlueprint]
  adjoin_defined := .mk fun v => by
    simp [rawEmissionBlueprint,pair_defined.iff,sub_defined.iff,rawConsDef_eval]
    constructor
    · rintro ⟨a,t,shape,returned⟩
      simpa [shape] using returned
    · intro returned
      exact ⟨π₁ (v 1),π₂ (v 1),(pair_unpair (v 1)).symm,returned⟩

/-- Serialize an internal vector with unbiased arity and a fixed tag
offset. Its length and both numeric tails can be nonstandard. -/
noncomputable def emitRaw (tokens suffix offset : M) : M :=
  rawEmissionConstruction.result ![suffix,offset] tokens

@[simp] theorem emitRaw_nil (suffix offset : M) : emitRaw 0 suffix offset = suffix := by
  simp [emitRaw,rawEmissionConstruction]

@[simp] theorem emitRaw_cons (token tokens suffix offset : M) :
    emitRaw (token ∷ tokens) suffix offset =
      rawCons (π₁ token) (π₂ token-offset) (emitRaw tokens suffix offset) := by
  simp [emitRaw,rawEmissionConstruction]

@[definability] instance emitRaw_definable : 𝚺ᴬ₁-Function₃ (emitRaw (M := M)) := by
  have graph := (rawEmissionConstruction.result_defined (V := M)).to_definable
  have parameters (v : Fin 4 → M) : (fun i : Fin 2 => v i.succ.succ) = ![v 2,v 3] := by
    funext i
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl <;> rfl
  change 𝚺ᴬ₁.Definable (fun v : Fin 4 → M => v 0 = emitRaw (v 1) (v 2) (v 3))
  change 𝚺ᴬ₁.Definable (fun v : Fin 4 → M => v 0 =
    rawEmissionConstruction.result (fun i : Fin 2 => v i.succ.succ) (v 1)) at graph
  simpa only [parameters,emitRaw] using graph

/-- The first token of a guarded scan is in the permitted tag range. -/
def guardedStep (offset x y : M) : Prop :=
  ∃ token rest, 0 < π₂ x ∧ π₁ x = token ∷ rest ∧ offset ≤ π₂ token ∧
    y = ⟪rest, π₂ x-1+π₁ token⟫

def GuardedConsumes (offset tokens before after : M) : Prop :=
  Chain (guardedStep offset) (len tokens) ⟪tokens,before⟫ ⟪0,after⟫

theorem guardedStep_definable (offset : M) : 𝚺ᴬ₁-Relation (guardedStep offset) := by
  unfold guardedStep
  definability

theorem guardedConsumes_definable : 𝚺ᴬ₁-Relation₄ (GuardedConsumes (M := M)) := by
  unfold GuardedConsumes Chain guardedStep
  definability

end PalomarI3334.SearchProgram
