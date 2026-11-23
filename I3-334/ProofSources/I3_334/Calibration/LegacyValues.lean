module
public import I3_334.Calibration.ModelQuotient
public import I3_334Support.Calibration.GroundTerms
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380
open PalomarI3380.Calibration (FilterLanguage FunctionSymbol)
open ArithmeticMachine.SourceWords
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def legacyConst (tag : Nat) : M :=
  modelApplication (tag : M) []

noncomputable def legacyUnary (tag : Nat) (a : M) : M :=
  modelApplication (tag : M) [a]

noncomputable def legacyBinary (tag : Nat) (a b : M) : M :=
  modelApplication (tag : M) [a,b]

@[definability] theorem legacyUnary_definable (tag : Nat) : 𝚺ᴬ₁-Function₁ (legacyUnary (M := M) tag) := by
  change 𝚺ᴬ₁.Definable (fun v : Fin 2 → M => v 0 = legacyUnary tag (v 1))
  simp only [legacyUnary,modelApplication,joinVectors,appendVector_empty_suffix]
  definability

@[definability] theorem legacyBinary_definable (tag : Nat) : 𝚺ᴬ₁-Function₂ (legacyBinary (M := M) tag) := by
  change 𝚺ᴬ₁.Definable (fun v : Fin 3 → M => v 0 = legacyBinary tag (v 1) (v 2))
  simp only [legacyBinary,modelApplication,joinVectors,appendVector_empty_suffix]
  definability

noncomputable def legacyTop : M := legacyBinary 3 (legacyUnary 3 (legacyConst 2)) (legacyConst 2)
noncomputable def legacyMeet (a b : M) : M := legacyUnary 3 (legacyBinary 3 a b)

@[definability] theorem legacyMeet_definable : 𝚺ᴬ₁-Function₂ (legacyMeet (M := M)) := by
  letI : 𝚺ᴬ₁-Function₁ (legacyUnary (M := M) 3) := legacyUnary_definable 3
  exact Bounding.HierarchySymbol.DefinableFunction₁.comp (F := legacyUnary 3)
    (legacyBinary_definable 3)

/-- Arithmetic version of the reserved-code test in the recovered algebra. -/
def SafeCode (a : M) : Prop := ∃ t, ClosedVector 3 t ∧ ModelDerives t a

theorem safeCode_definable : 𝚺ᴬ₁-Predicate (SafeCode (M := M)) := by
  have validity := closedVector_definable (M := M)
  have rewrites := modelDerives_definable (M := M)
  unfold SafeCode
  definability

theorem safeCode_class (a : M) : SafeCode a ↔ ModelSafe (modelClass a) := by
  simp [SafeCode,ModelSafe,modelClass_eq]

noncomputable def legacyLocal (a : M) : M := by
  classical
  exact if π₂ a = 0 ∧ SafeCode (π₁ a) then π₁ a else legacyConst 3

theorem legacyLocal_definable : 𝚺ᴬ_[2]-Function₁ (legacyLocal (M := M)) := by
  let P := fun x : M => π₂ x = 0 ∧ SafeCode (π₁ x)
  have valid := safeCode_definable (M := M)
  have p : 𝚺ᴬ₁-Predicate P := by unfold P; definability
  have pYes : 𝚺ᴬ_[2]-Predicate P := p.of_lt (by decide)
  have neg : 𝚷ᴬ_[1]-Predicate (fun x => ¬P x) := Bounding.HierarchySymbol.Definable.not (Γ := 𝚷) p
  have pNo : 𝚺ᴬ_[2]-Predicate (fun x => ¬P x) := neg.of_lt (by decide)
  have form : 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M =>
      (P (v 1) ∧ v 0 = π₁ (v 1)) ∨ (¬P (v 1) ∧ v 0 = legacyConst 3)) := by
    have yes : 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => v 0 = π₁ (v 1)) := by definability
    have no : 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => v 0 = legacyConst 3) := by definability
    exact ((pYes.retraction (fun _ => 1)).and yes).or ((pNo.retraction (fun _ => 1)).and no)
  refine form.of_iff (fun v => ?_)
  classical
  by_cases h : P (v 1)
  · simp [legacyLocal,show π₂ (v 1) = 0 ∧ SafeCode (π₁ (v 1)) from h,h]
  · simp [legacyLocal,show ¬(π₂ (v 1) = 0 ∧ SafeCode (π₁ (v 1))) from h,h]

noncomputable def legacyLeftProduct (a b : M) : M := legacyBinary 4 a (legacyUnary 4 b)

@[definability] theorem legacyLeftProduct_definable :
    𝚺ᴬ₁-Function₂ (legacyLeftProduct (M := M)) := by
  letI : 𝚺ᴬ₁-Function₂ (legacyBinary (M := M) 4) := legacyBinary_definable 4
  exact Bounding.HierarchySymbol.DefinableFunction₂.comp (F := legacyBinary 4)
    (.var 0) ((legacyUnary_definable 4).retraction ![1])

noncomputable def legacyNode (a b c : M) : M :=
  legacyMeet (legacyLeftProduct (legacyLocal a) (legacyLocal b))
    (legacyBinary 3 (legacyLocal b) (legacyLocal c))

theorem legacyNode_definable : 𝚺ᴬ_[2]-Function₃ (legacyNode (M := M)) := by
  have localDef := legacyLocal_definable (M := M)
  have meetDef : 𝚺ᴬ_[2]-Function₂ (legacyMeet (M := M)) := legacyMeet_definable.of_lt (by decide)
  have prodDef : 𝚺ᴬ_[2]-Function₂ (legacyLeftProduct (M := M)) := legacyLeftProduct_definable.of_lt (by decide)
  have binDef : 𝚺ᴬ_[2]-Function₂ (legacyBinary (M := M) 3) := (legacyBinary_definable 3).of_lt (by decide)
  unfold legacyNode
  definability

noncomputable def legacySubset : M :=
  legacyUnary 3 (legacyBinary 4 (legacyUnary 4 (legacyConst 2)) (legacyUnary 3 (legacyConst 2)))

noncomputable def legacyStages : M :=
  let choose := legacyUnary 1 (legacySubset : M)
  legacyBinary 4 (legacyUnary 4 choose) choose

noncomputable def legacyConstant : Constant → M
  | .D => ⟪legacyConst 1,0⟫
  | .J => ⟪legacyConst 0,0⟫
  | .E => ⟪legacyConst 2,0⟫
  | .I => ⟪legacyConst 5,1⟫
  | .U => ⟪legacyTop,1⟫
  | .T => ⟪legacySubset,1⟫
  | .S => ⟪legacyStages,1⟫

noncomputable def legacyComplement (a : M) : M :=
  ⟪legacyUnary 3 (π₁ a),1-π₂ a⟫

noncomputable def legacyConverse (a : M) : M :=
  ⟪legacyUnary 4 (π₁ a),π₂ a⟫

noncomputable def legacyChoice (a : M) : M :=
  ⟪legacyMeet (legacyUnary 1 (π₁ a)) (π₁ a),π₂ a⟫

noncomputable def legacyNand (a b : M) : M :=
  ⟪legacyBinary 3 (π₁ a) (π₁ b),1-π₂ a*π₂ b⟫

noncomputable def legacyProduct (a b : M) : M :=
  ⟪legacyBinary 4 (π₁ a) (π₁ b),1-(1-π₂ a*π₂ b)⟫

noncomputable def legacyCodedLocal (a : M) : M := ⟪legacyLocal a,0⟫
noncomputable def legacyCodedNode (a b c : M) : M := ⟪legacyNode a b c,0⟫

noncomputable def legacyApplication : {k : Nat} → FunctionSymbol k → (Fin k → M) → M
  | _, .constant c, _ => legacyConstant c
  | _, .complement, a => legacyComplement (a 0)
  | _, .converse, a => legacyConverse (a 0)
  | _, .choose, a => legacyChoice (a 0)
  | _, .localRelation, a => legacyCodedLocal (a 0)
  | _, .nand, a => legacyNand (a 0) (a 1)
  | _, .product, a => legacyProduct (a 0) (a 1)
  | _, .node, a => legacyCodedNode (a 0) (a 1) (a 2)

end PalomarI3334.SearchProgram
