module
public import I3_334.Calibration.LegacyValues
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380
open PalomarI3380.Calibration (FunctionSymbol)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ValidLegacy (a : M) : Prop := ClosedVector 0 (π₁ a)

theorem validLegacy_definable : 𝚺ᴬ₁-Predicate (ValidLegacy (M := M)) := by
  have typed := closedVector_definable (M := M)
  unfold ValidLegacy
  definability

noncomputable def legacyNative (word : M) : ClosedClass M := by
  classical
  exact if h : ClosedVector 0 word then closedClass word h else modelClosedAlgebra.seed

noncomputable def legacyValue (a : M) : ClosedClass M × Bool :=
  (legacyNative (π₁ a),decide (π₂ a ≠ 0))

noncomputable abbrev legacyModel : Algebra (ClosedClass M × Bool) :=
  (modelClosedAlgebra (M := M)).legacy (ModelSafe ∘ Subtype.val)

theorem legacyModel_models : (legacyModel (M := M)).Models Manifest.preceding :=
  (modelClosedAlgebra (M := M)).legacy_models (ModelSafe ∘ Subtype.val)
    modelClosedAlgebra_models modelSafe_closed_constructor

theorem legacyNative_valid {w : M} (good : ClosedVector 0 w) :
    legacyNative w = closedClass w good := by
  classical
  simp [legacyNative,good]

theorem legacyConst_valid (tag : Nat) : ClosedVector 0 (legacyConst (M := M) tag) :=
  closed_application 0 _ [] (Arithmetic.zero_le _) (by simp)

theorem legacyUnary_valid (tag : Nat) {a : M} (good : ClosedVector 0 a) :
    ClosedVector 0 (legacyUnary tag a) :=
  closed_application 0 _ [a] (Arithmetic.zero_le _) (by simpa using good)

theorem legacyBinary_valid (tag : Nat) {a b : M} (goodA : ClosedVector 0 a) (goodB : ClosedVector 0 b) :
    ClosedVector 0 (legacyBinary tag a b) :=
  closed_application 0 _ [a,b] (Arithmetic.zero_le _) (by simpa using And.intro goodA goodB)

theorem legacyNative_const (tag : Nat) : legacyNative (legacyConst (M := M) tag) = closedApply tag [] := by
  rw [legacyNative_valid (legacyConst_valid _)]
  rfl

theorem legacyNative_unary (tag : Nat) {a : M} (good : ClosedVector 0 a) :
    legacyNative (legacyUnary tag a) = closedApply tag [legacyNative a] := by
  apply Subtype.ext
  rw [legacyNative_valid (legacyUnary_valid tag good),closedApply_value,legacyNative_valid good]
  exact (quotientApply_class tag [a]).symm

theorem legacyNative_binary (tag : Nat) {a b : M} (goodA : ClosedVector 0 a) (goodB : ClosedVector 0 b) :
    legacyNative (legacyBinary tag a b) = closedApply tag [legacyNative a,legacyNative b] := by
  apply Subtype.ext
  rw [legacyNative_valid (legacyBinary_valid tag goodA goodB),closedApply_value,
    legacyNative_valid goodA,legacyNative_valid goodB]
  exact (quotientApply_class tag [a,b]).symm

theorem legacyMeet_valid {a b : M} (goodA : ClosedVector 0 a) (goodB : ClosedVector 0 b) :
    ClosedVector 0 (legacyMeet a b) :=
  legacyUnary_valid 3 (legacyBinary_valid 3 goodA goodB)

theorem legacyNative_meet {a b : M} (goodA : ClosedVector 0 a) (goodB : ClosedVector 0 b) :
    legacyNative (legacyMeet a b) = (modelClosedAlgebra (M := M)).meet (legacyNative a) (legacyNative b) := by
  rw [legacyMeet,legacyNative_unary 3 (legacyBinary_valid 3 goodA goodB),legacyNative_binary 3 goodA goodB]
  rfl

theorem legacyLocal_valid {a : M} (good : ValidLegacy a) : ClosedVector 0 (legacyLocal a) := by
  unfold legacyLocal
  split
  · exact good
  · exact legacyConst_valid 3

theorem legacyNative_local {a : M} (good : ValidLegacy a) :
    legacyNative (legacyLocal a) =
      (modelClosedAlgebra (M := M)).decodeLocal (ModelSafe ∘ Subtype.val) (legacyValue a) := by
  classical
  have safe : SafeCode (π₁ a) ↔ ModelSafe (legacyNative (π₁ a)).val := by
    rw [legacyNative_valid good]
    exact safeCode_class _
  unfold legacyLocal NativeAlgebra.decodeLocal
  change (legacyNative (if π₂ a = 0 ∧ SafeCode (π₁ a) then π₁ a else legacyConst 3)) =
    (if decide (π₂ a ≠ 0) = true then modelClosedAlgebra.seed
      else if ModelSafe (legacyNative (π₁ a)).val then legacyNative (π₁ a) else modelClosedAlgebra.seed)
  by_cases bit : π₂ a = 0 <;> by_cases guard : SafeCode (π₁ a) <;>
    simp [bit,guard,← safe,legacyNative_const,modelClosedAlgebra]

theorem legacySubset_valid : ClosedVector 0 (legacySubset (M := M)) :=
  legacyUnary_valid 3 (legacyBinary_valid 4 (legacyUnary_valid 4 (legacyConst_valid 2))
    (legacyUnary_valid 3 (legacyConst_valid 2)))

theorem legacyTop_valid : ClosedVector 0 (legacyTop (M := M)) :=
  legacyBinary_valid 3 (legacyUnary_valid 3 (legacyConst_valid 2)) (legacyConst_valid 2)

theorem legacyStages_valid : ClosedVector 0 (legacyStages (M := M)) :=
  legacyBinary_valid 4 (legacyUnary_valid 4 (legacyUnary_valid 1 legacySubset_valid))
    (legacyUnary_valid 1 legacySubset_valid)

theorem legacyNative_subset : legacyNative (legacySubset (M := M)) = modelClosedAlgebra.subsetValue := by
  have e := legacyConst_valid (M := M) 2
  unfold legacySubset
  rw [legacyNative_unary 3 (legacyBinary_valid 4 (legacyUnary_valid 4 e) (legacyUnary_valid 3 e)),
    legacyNative_binary 4 (legacyUnary_valid 4 e) (legacyUnary_valid 3 e),
    legacyNative_unary 4 e, legacyNative_unary 3 e, legacyNative_const]
  rfl

theorem legacyNative_stages : legacyNative (legacyStages (M := M)) = modelClosedAlgebra.stageValue := by
  have p := legacyUnary_valid 1 (legacySubset_valid (M := M))
  unfold legacyStages
  dsimp only
  rw [legacyNative_binary 4 (legacyUnary_valid 4 p) p, legacyNative_unary 4 p,
    legacyNative_unary 1 legacySubset_valid,legacyNative_subset]
  rfl

theorem legacyNative_top : legacyNative (legacyTop (M := M)) = modelClosedAlgebra.topValue := by
  have e := legacyConst_valid (M := M) 2
  unfold legacyTop
  rw [legacyNative_binary 3 (legacyUnary_valid 3 e) e,legacyNative_unary 3 e,legacyNative_const]
  exact modelClosedAlgebra.top_literal modelClosedAlgebra_models.boolean

theorem legacyConstant_valid (c : Constant) : ValidLegacy (legacyConstant (M := M) c) := by
  cases c <;>
    simp only [legacyConstant,ValidLegacy,Arithmetic.pi₁_pair]
  · exact legacyConst_valid 1
  · exact legacyConst_valid 0
  · exact legacyTop_valid
  · exact legacyConst_valid 2
  · exact legacyConst_valid 5
  · exact legacySubset_valid
  · exact legacyStages_valid

theorem legacyConstant_value (c : Constant) : legacyValue (legacyConstant (M := M) c) =
    (legacyModel (M := M)).constant c := by
  cases c <;> apply Prod.ext
  all_goals
    simp only [legacyConstant,legacyValue,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,
      NativeAlgebra.legacy,NativeAlgebra.relationAlgebra,NativeAlgebra.selectorAlgebra,
      legacyNative_const,legacyNative_subset,legacyNative_stages,legacyNative_top]
  all_goals first | rfl | simp [Arithmetic.one_ne_zero]

theorem legacyApplication_valid {n : Nat} (f : FunctionSymbol n) (a : Fin n → M)
    (good : ∀ i, ValidLegacy (a i)) : ValidLegacy (legacyApplication f a) := by
  cases f
  case constant c => exact legacyConstant_valid c
  case complement => simpa only [legacyApplication,legacyComplement,ValidLegacy,Arithmetic.pi₁_pair]
    using legacyUnary_valid 3 (good 0)
  case converse => simpa only [legacyApplication,legacyConverse,ValidLegacy,Arithmetic.pi₁_pair]
    using legacyUnary_valid 4 (good 0)
  case choose => simpa only [legacyApplication,legacyChoice,ValidLegacy,Arithmetic.pi₁_pair]
    using legacyMeet_valid (legacyUnary_valid 1 (good 0)) (good 0)
  case localRelation => simpa only [legacyApplication,legacyCodedLocal,ValidLegacy,Arithmetic.pi₁_pair]
    using legacyLocal_valid (good 0)
  case nand => simpa only [legacyApplication,legacyNand,ValidLegacy,Arithmetic.pi₁_pair]
    using legacyBinary_valid 3 (good 0) (good 1)
  case product => simpa only [legacyApplication,legacyProduct,ValidLegacy,Arithmetic.pi₁_pair]
    using legacyBinary_valid 4 (good 0) (good 1)
  case node =>
    simp only [legacyApplication,legacyCodedNode,ValidLegacy,Arithmetic.pi₁_pair,legacyNode,legacyLeftProduct]
    exact legacyMeet_valid (legacyBinary_valid 4 (legacyLocal_valid (good 0))
      (legacyUnary_valid 4 (legacyLocal_valid (good 1))))
      (legacyBinary_valid 3 (legacyLocal_valid (good 1)) (legacyLocal_valid (good 2)))

noncomputable def legacyAlgebraApply : {n : Nat} → FunctionSymbol n → (Fin n → ClosedClass M × Bool) →
    ClosedClass M × Bool
  | _, .constant c, _ => legacyModel.constant c
  | _, .complement, v => legacyModel.neg (v 0)
  | _, .converse, v => legacyModel.converse (v 0)
  | _, .choose, v => legacyModel.choice (v 0)
  | _, .localRelation, v => legacyModel.localRel (v 0)
  | _, .nand, v => legacyModel.nand (v 0) (v 1)
  | _, .product, v => legacyModel.product (v 0) (v 1)
  | _, .node, v => legacyModel.node (v 0) (v 1) (v 2)

@[simp] theorem legacy_item (word bit : M) :
    legacyValue (⟪word,bit⟫ : M) = (legacyNative word,decide (bit ≠ 0)) := by
  simp only [legacyValue,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair]

private theorem bit_complement (b : M) : decide (1-b ≠ 0) = !(decide (b ≠ 0)) := by
  by_cases h : b = 0
  · simp [h,Arithmetic.one_ne_zero]
  · have bound : (1 : M) ≤ b := pos_iff_one_le.mp (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm h))
    simp [Arithmetic.sub_spec_of_le bound,h]

private theorem bit_product (a b : M) :
    decide (a*b ≠ 0) = ((decide (a ≠ 0)) && (decide (b ≠ 0))) := by
  by_cases h : a = 0 <;> by_cases k : b = 0 <;> simp [h,k,mul_eq_zero]

/-- Evaluate a single source symbol in the recovered algebra. The arithmetic
word carries a representative of the first component and one Boolean flag. -/
theorem legacyApplication_value {n : Nat} (f : FunctionSymbol n) (a : Fin n → M)
    (good : ∀ i, ValidLegacy (a i)) :
    legacyValue (legacyApplication f a) = legacyAlgebraApply f (legacyValue ∘ a) := by
  cases f
  case constant c => exact legacyConstant_value c
  case complement =>
    refine (legacy_item ..).trans (Prod.ext ?_ (bit_complement _))
    exact legacyNative_unary 3 (good 0)
  case converse =>
    refine (legacy_item ..).trans (Prod.ext ?_ rfl)
    exact legacyNative_unary 4 (good 0)
  case choose =>
    refine (legacy_item ..).trans (Prod.ext ?_ rfl)
    have h : ClosedVector 0 (π₁ (a 0)) := good 0
    rw [legacyNative_meet (legacyUnary_valid 1 h) h,legacyNative_unary 1 h]
    rfl
  case localRelation =>
    refine (legacy_item ..).trans (Prod.ext ?_ (by change decide ((0 : M) ≠ 0) = false; simp))
    exact legacyNative_local (good 0)
  case nand =>
    refine (legacy_item ..).trans (Prod.ext ?_ ?_)
    · exact legacyNative_binary 3 (good 0) (good 1)
    · exact (bit_complement _).trans (congrArg Bool.not (bit_product _ _))
  case product =>
    refine (legacy_item ..).trans (Prod.ext ?_ ?_)
    · exact legacyNative_binary 4 (good 0) (good 1)
    · exact (bit_complement _).trans
        ((congrArg Bool.not (bit_complement _)).trans ((Bool.not_not _).trans (bit_product _ _)))
  case node =>
    refine (legacy_item ..).trans (Prod.ext ?_ (by change decide ((0 : M) ≠ 0) = false; simp))
    have l := legacyLocal_valid (good 0)
    have m := legacyLocal_valid (good 1)
    have r := legacyLocal_valid (good 2)
    change legacyNative (legacyNode (a 0) (a 1) (a 2)) = _
    unfold legacyNode legacyLeftProduct
    rw [legacyNative_meet (legacyBinary_valid 4 l (legacyUnary_valid 4 m)) (legacyBinary_valid 3 m r),
      legacyNative_binary 4 l (legacyUnary_valid 4 m),legacyNative_unary 4 m,
      legacyNative_binary 3 m r,legacyNative_local (good 0),legacyNative_local (good 1),
      legacyNative_local (good 2)]
    rfl

end PalomarI3334.SearchProgram
