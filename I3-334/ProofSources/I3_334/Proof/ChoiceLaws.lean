module
public import I3_334.Proof.RelationLaws
public import I3_334Support.RelationAlgebra.Functional
@[expose] public section

namespace PalomarI3334.NativeAlgebra

open PalomarI3380
open Templates

variable {A : Type} {M : NativeAlgebra A}
variable {safe : A → Prop}

private abbrev core (M : NativeAlgebra A) : Algebra A :=
  M.relationAlgebra id (fun a _ _ => a)

private theorem core_laws (model : M.ModelsOn safe) : RelationLaws M.core :=
  model.relation_laws id (fun a _ _ => a)

private theorem core_top (model : M.ModelsOn safe) : M.core.top = M.topValue :=
  (core_laws model).universal_top.symm

theorem ModelsOn.nand_top_iff_le (model : M.ModelsOn safe) (x y : A) :
    M.nand x (M.neg y) = M.topValue ↔ M.le x y := by
  let B := model.boolean
  constructor
  · intro h
    exact (B.disjoint_iff_le M.membership x y).mp (congrArg M.neg h)
  · intro h
    have disjoint := (B.disjoint_iff_le M.membership x y).mpr h
    have equality := congrArg M.neg disjoint
    change M.neg (M.neg (M.nand x (M.neg y))) = M.neg (M.neg M.topValue) at equality
    simpa only [B.involution] using equality


theorem ModelsOn.rawChoice_function (model : M.ModelsOn safe) (a : A) :
    M.le (M.product (M.converse (M.choice a)) (M.choice a)) M.identity :=
  (model.nand_top_iff_le _ _).mp (model.factors_top a a a M.seed model.seed_safe).2.2.2.2.1

theorem ModelsOn.maskedChoice_function (model : M.ModelsOn safe) (a : A) :
    M.le (M.product (M.converse (M.maskedChoice a)) (M.maskedChoice a)) M.identity := by
  let laws := core_laws model
  exact laws.functional_mono (laws.bool.inf_le_left (M.choice a) a) (model.rawChoice_function a)

theorem ModelsOn.maskedChoice_subset (model : M.ModelsOn safe) (a : A) :
    M.le (M.maskedChoice a) a :=
  model.boolean.inf_le_right _ _

theorem ModelsOn.maskedChoice_domain (model : M.ModelsOn safe) (a : A) :
    M.product (M.maskedChoice a) M.topValue = M.product a M.topValue := by
  let laws := core_laws model
  have factor := (model.factors_top a a a M.seed model.seed_safe).2.2.2.1
  change M.nand a (M.neg (M.product (M.maskedChoice a)
    (M.nand (M.neg M.membership) M.membership))) = M.topValue at factor
  rw [M.top_literal model.boolean] at factor
  have coverage : M.le a (M.product (M.maskedChoice a) M.topValue) :=
    (model.nand_top_iff_le _ _).mp factor
  have top_idem : M.product M.topValue M.topValue = M.topValue := by
    have unitBelow : M.core.le (M.core.constant .I) (M.core.constant .U) := by
      rw [laws.universal_top]
      exact laws.bool.le_top _ _
    have lower := laws.mul_mono_left unitBelow (M.core.constant .U)
    rw [laws.unit_left] at lower
    exact laws.bool.le_antisymm (laws.bool.le_top _ _) lower
  have lower := laws.mul_mono_left coverage M.topValue
  change M.le (M.product a M.topValue)
    (M.product (M.product (M.maskedChoice a) M.topValue) M.topValue) at lower
  rw [show M.product (M.product (M.maskedChoice a) M.topValue) M.topValue =
    M.product (M.maskedChoice a) (M.product M.topValue M.topValue) from
      laws.mul_assoc _ _ _, top_idem] at lower
  exact laws.bool.le_antisymm (laws.mul_mono_left (model.maskedChoice_subset a) M.topValue) lower

theorem ModelsOn.subset_refl (model : M.ModelsOn safe) : M.le M.identity M.subsetValue := by
  let laws := core_laws model
  have h : M.core.le (M.core.product (M.core.converse M.membership) (M.core.neg M.membership))
      (M.core.neg (M.core.constant .I)) := by
    apply (laws.residual _ _ _).mpr
    rw [laws.conv_inv, laws.bool.involution, laws.unit_right]
    exact laws.bool.le_refl _
  change M.le (M.product (M.converse M.membership) (M.neg M.membership)) (M.neg M.identity) at h
  apply (model.boolean.neg_order M.identity M.subsetValue).mp
  simpa only [subsetValue, model.boolean.involution] using h

/-- The masked chooser agrees with the raw chooser on the subset relation. -/
theorem ModelsOn.choice_subset_agrees (model : M.ModelsOn safe) :
    M.maskedChoice M.subsetValue = M.choice M.subsetValue := by
  let laws := core_laws model
  have subsetUnit : M.core.le (M.core.constant .I) M.subsetValue := model.subset_refl
  have full : M.product M.subsetValue M.topValue = M.topValue := by
    have lower := laws.mul_mono_left subsetUnit (M.core.constant .U)
    rw [laws.unit_left] at lower
    exact laws.bool.le_antisymm (laws.bool.le_top _ _) lower
  have masked : M.product (M.maskedChoice M.subsetValue) M.topValue = M.topValue :=
    (model.maskedChoice_domain _).trans full
  have smaller := laws.bool.inf_le_left (M.choice M.subsetValue) M.subsetValue
  have raw : M.product (M.choice M.subsetValue) M.topValue = M.topValue := by
    have lower := laws.mul_mono_left smaller M.topValue
    change M.le (M.product (M.maskedChoice M.subsetValue) M.topValue) _ at lower
    rw [masked] at lower
    exact laws.bool.le_antisymm (laws.bool.le_top _ _) lower
  apply laws.functional_eq_of_support (model.rawChoice_function _) smaller
  unfold RelationLaws.support
  rw [core_top model]
  change M.meet M.identity (M.product (M.maskedChoice M.subsetValue) M.topValue) =
    M.meet M.identity (M.product (M.choice M.subsetValue) M.topValue)
  rw [masked, raw]

/-- The guarded factor is an inequality for the value of each allowed
closed operand, via the recovered right adjoint. -/
theorem ModelsOn.guarded_preservation (model : M.ModelsOn safe) (d : A) (guarded : safe d) :
    M.le (M.product (M.converse M.embedding) (M.product d M.embedding)) d := by
  let laws := core_laws model
  let value := d
  have factor : M.nand (M.product value M.embedding) (M.product M.embedding (M.neg value)) =
      M.topValue := (model.factors_top M.seed M.seed M.seed d guarded).2.2.1
  have inclusion : M.le (M.product value M.embedding)
      (M.neg (M.product M.embedding (M.neg value))) := by
    apply (model.nand_top_iff_le _ _).mp
    simpa only [model.boolean.involution] using factor
  change M.core.le (M.core.product (M.core.converse M.embedding) (M.core.product value M.embedding)) value
  apply (laws.residual _ _ _).mpr
  rw [laws.conv_inv]
  exact inclusion

end PalomarI3334.NativeAlgebra
