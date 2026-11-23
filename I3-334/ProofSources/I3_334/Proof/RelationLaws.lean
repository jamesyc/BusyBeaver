module
public import I3_334.Proof.GuardedAlgebra
public import I3_334Support.RelationAlgebra.Laws
@[expose] public section

namespace PalomarI3334.NativeAlgebra

open PalomarI3380
open Templates

variable {A : Type} (M : NativeAlgebra A)
variable {safe : A → Prop}

abbrev le (x y : A) : Prop := MeredithLaws.Le M.meet x y
def topValue : A := MeredithLaws.top M.meet M.neg M.membership
def bottomValue : A := M.neg M.topValue
def maskedChoice (a : A) : A := M.meet (M.choice a) a

def subsetValue : A := M.neg (M.product (M.converse M.membership) (M.neg M.membership))

def stageValue : A :=
  M.product (M.converse (M.choice M.subsetValue)) (M.choice M.subsetValue)

theorem top_literal (laws : MeredithLaws M.meet M.neg) :
    M.nand (M.neg M.membership) M.membership = M.topValue := by
  simp only [topValue, MeredithLaws.top, MeredithLaws.sup, meet, laws.involution]

private theorem top_components (laws : MeredithLaws M.meet M.neg) {x y : A}
    (both : M.meet x y = M.topValue) : x = M.topValue ∧ y = M.topValue := by
  have left := laws.inf_le_left x y
  have right := laws.inf_le_right x y
  rw [both] at left right
  exact ⟨laws.le_antisymm (laws.le_top M.membership x) left,
    laws.le_antisymm (laws.le_top M.membership y) right⟩

theorem ModelsOn.factors_top {M : NativeAlgebra A} (model : M.ModelsOn safe) (a b c : A)
    (d : A) (guarded : safe d) :
    let v := valuation a b c d
    M.eval v factorImage = M.topValue ∧ M.eval v factorAdjunction = M.topValue ∧
      M.eval v factorPreservation = M.topValue ∧ M.eval v factorCoverage = M.topValue ∧
      M.eval v factorFunction = M.topValue ∧ M.eval v factorExtensionality = M.topValue := by
  let v := valuation a b c d
  have bundle := model.equations guarded_bundle (by simp [Templates.equations]) a b c d guarded
  change M.meet (M.eval v factorImage) (M.meet (M.eval v factorAdjunction)
    (M.meet (M.eval v factorPreservation) (M.meet (M.eval v factorCoverage)
      (M.meet (M.eval v factorFunction) (M.eval v factorExtensionality))))) =
      M.nand (M.neg M.membership) M.membership at bundle
  rw [M.top_literal model.boolean] at bundle
  obtain ⟨image, rest⟩ := M.top_components model.boolean bundle
  obtain ⟨adjoint, rest⟩ := M.top_components model.boolean rest
  obtain ⟨preservation, rest⟩ := M.top_components model.boolean rest
  obtain ⟨coverage, rest⟩ := M.top_components model.boolean rest
  obtain ⟨functional, extensionality⟩ := M.top_components model.boolean rest
  exact ⟨image, adjoint, preservation, coverage, functional, extensionality⟩

theorem ModelsOn.nand_converse {M : NativeAlgebra A} (model : M.ModelsOn safe) (x y : A) :
    M.nand (M.converse x) (M.converse y) = M.converse (M.nand x y) :=
  model.equations converse_nand (by simp [Templates.equations]) x y x M.seed model.seed_safe

theorem ModelsOn.converse_neg {M : NativeAlgebra A} (model : M.ModelsOn safe) (a : A) :
    M.converse (M.neg a) = M.neg (M.converse a) := by
  have nand_self (x : A) : M.nand x x = M.neg x := by
    have equality := congrArg M.neg (model.boolean.idempotent x)
    change M.neg (M.neg (M.nand x x)) = M.neg x at equality
    simpa only [model.boolean.involution] using equality
  have same := (model.nand_converse a a).symm
  rwa [nand_self a, nand_self (M.converse a)] at same

theorem ModelsOn.combined_adjoint {M : NativeAlgebra A} (model : M.ModelsOn safe) (a b c : A) :
    M.le (M.product (M.converse a) (M.meet (M.neg (M.product a b)) c)) (M.neg b) := by
  let x := M.product (M.converse a) (M.meet (M.neg (M.product a b)) c)
  have factor : M.nand x b = M.topValue :=
    (model.factors_top a b c M.seed model.seed_safe).2.1
  apply (model.boolean.disjoint_iff_le M.membership x (M.neg b)).mp
  rw [model.boolean.involution]
  exact congrArg M.neg factor

/-- Extend the core operations by interpretations of the two auxiliary
symbols from the older signature. The relation laws do not use them. -/
def relationAlgebra (localRel : A → A) (node : A → A → A → A) : Algebra A where
  constant
    | .D => M.domain
    | .J => M.embedding
    | .E => M.membership
    | .I => M.identity
    | .U => M.topValue
    | .T => M.subsetValue
    | .S => M.stageValue
  neg := M.neg
  converse := M.converse
  choice := M.maskedChoice
  localRel := localRel
  nand := M.nand
  product := M.product
  node := node

/-- The bundled adjunction law supplies both right monotonicity and
converse involution before any representation theorem is used. -/
theorem ModelsOn.relation_laws {M : NativeAlgebra A} (model : M.ModelsOn safe)
    (localRel : A → A) (node : A → A → A → A) : RelationLaws (M.relationAlgebra localRel node) := by
  let B := model.boolean
  let adjoint := fun a z => M.neg (M.product (M.converse a) (M.neg z))
  have peirce (a b : A) : M.le (M.product (M.converse a) (M.neg (M.product a b))) (M.neg b) := by
    have h := model.combined_adjoint a b M.topValue
    have identity : M.meet (M.neg (M.product a b)) M.topValue = M.neg (M.product a b) :=
      B.le_top M.membership _
    rwa [identity] at h
  have unit (a b : A) : M.le b (adjoint a (M.product a b)) := by
    have h := (B.neg_order _ _).mpr (peirce a b)
    simpa only [adjoint, B.involution] using h
  have lower (a z t : A) :
      M.le (M.product (M.converse (M.converse a)) (M.meet (adjoint a z) t)) z := by
    simpa only [adjoint, B.involution] using model.combined_adjoint (M.converse a) (M.neg z) t
  have below (a : A) : M.le (M.converse (M.converse a)) a := by
    have bound := unit a M.identity
    have meetEq : M.meet (adjoint a (M.product a M.identity)) M.identity = M.identity :=
      (B.commutative _ _).trans bound
    have h := lower a (M.product a M.identity) M.identity
    rw [meetEq, model.unit, model.unit] at h
    exact h
  have involution (a : A) : M.converse (M.converse a) = a := by
    have reverse := below (M.neg a)
    rw [model.converse_neg, model.converse_neg] at reverse
    exact B.le_antisymm (below a) ((B.neg_order _ _).mp reverse)
  refine ⟨B, fun x y z => (model.associative x y z).symm, model.unit,
    involution, ?_, ?_, ?_⟩
  · intro p q hpq a
    change M.le p q at hpq
    have bound := B.le_trans hpq (unit a q)
    have meetEq : M.meet (adjoint a (M.product a q)) p = p :=
      (B.commutative _ _).trans bound
    have h := lower a (M.product a q) p
    rwa [meetEq, involution] at h
  · intro a b
    change M.converse (M.neg (M.nand a b)) = M.neg (M.nand (M.converse a) (M.converse b))
    rw [model.converse_neg, model.nand_converse]
  · intro a b
    change M.meet (M.product (M.converse a) (M.neg (M.product a b))) b = M.bottomValue
    have h := (B.disjoint_iff_le M.membership _ _).mpr (peirce a b)
    rwa [B.involution] at h

end PalomarI3334.NativeAlgebra
