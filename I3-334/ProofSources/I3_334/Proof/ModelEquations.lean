module
public import I3_334.Proof.ChoiceLaws
@[expose] public section

namespace PalomarI3334.NativeAlgebra

open PalomarI3380 Templates

variable {A : Type} {M : NativeAlgebra A}
variable {safe : A → Prop}

theorem ModelsOn.image_equation (model : M.ModelsOn safe) (a : A) :
    let image := M.product (M.converse M.membership) (M.maskedChoice a)
    M.product (M.meet (M.neg (M.product image (M.neg M.membership)))
      (M.neg (M.product (M.neg image) M.membership))) M.topValue = M.topValue := by
  let rel := M.maskedChoice a
  let image := M.product (M.converse M.membership) rel
  have law := (model.factors_top a a a M.seed model.seed_safe).1
  change M.product (M.meet
    (M.neg (M.product (M.neg image) M.membership))
    (M.neg (M.product (M.converse M.membership) (M.product rel (M.neg M.membership)))))
    (M.nand (M.neg M.membership) M.membership) = M.topValue at law
  rw [M.top_literal model.boolean, model.boolean.commutative, model.associative] at law
  exact law

theorem ModelsOn.extensionality (model : M.ModelsOn safe) :
    M.meet M.subsetValue (M.converse M.subsetValue) = M.identity := by
  have law := (model.factors_top M.seed M.seed M.seed M.seed model.seed_safe).2.2.2.2.2
  change M.nand (M.converse M.subsetValue) (M.meet M.subsetValue (M.neg M.identity)) =
    M.topValue at law
  have zero := congrArg M.neg law
  change M.meet (M.converse M.subsetValue) (M.meet M.subsetValue (M.neg M.identity)) =
    M.bottomValue at zero
  rw [← model.boolean.associative, model.boolean.commutative (M.converse M.subsetValue)] at zero
  apply model.boolean.le_antisymm
  · exact (model.boolean.disjoint_iff_le M.membership _ _).mp zero
  · let laws := model.relation_laws id (fun a _ _ => a)
    have conv := laws.conv_mono model.subset_refl
    change M.le (M.converse M.identity) (M.converse M.subsetValue) at conv
    rw [show M.converse M.identity = M.identity from laws.conv_unit] at conv
    exact model.boolean.le_inf.mpr ⟨model.subset_refl, conv⟩

theorem ModelsOn.domain_equation (model : M.ModelsOn safe) :
    M.meet M.identity (M.product M.embedding M.topValue) = M.domain := by
  have law := model.equations Templates.domain (by simp [Templates.equations]) M.seed M.seed M.seed
    M.seed model.seed_safe
  change M.meet M.identity (M.product M.embedding (M.nand (M.neg M.membership) M.membership)) =
    M.domain at law
  rwa [M.top_literal model.boolean] at law

theorem ModelsOn.stage_equation (model : M.ModelsOn safe) :
    M.product M.subsetValue (M.product M.stageValue (M.product M.membership M.stageValue)) =
      M.product M.membership M.stageValue :=
  model.equations Templates.stage_equation (by simp [Templates.equations]) M.seed M.seed M.seed M.seed model.seed_safe

theorem ModelsOn.stage_subidentity (model : M.ModelsOn safe) : M.le M.stageValue M.identity :=
  model.rawChoice_function M.subsetValue

theorem ModelsOn.domain_closed (model : M.ModelsOn safe) :
    M.meet M.identity (M.product M.membership (M.product (M.meet M.stageValue M.domain)
      M.topValue)) = M.domain := by
  let laws := model.relation_laws id (fun a _ _ => a)
  have law := model.equations Templates.domain_closure (by simp [Templates.equations]) M.seed M.seed M.seed
    M.seed model.seed_safe
  change M.meet M.identity (M.product M.seed (M.product M.stageValue
    (M.nand (M.neg M.membership) M.membership))) = M.domain at law
  rw [M.top_literal model.boolean, model.seed] at law
  have domain_sub : M.le M.domain M.identity := by
    rw [← model.domain_equation]
    exact model.boolean.inf_le_left _ _
  have fuse := laws.unit_product domain_sub model.stage_subidentity
  change M.product M.domain M.stageValue = M.meet M.domain M.stageValue at fuse
  have before : M.product (M.product M.membership M.domain) (M.product M.stageValue M.topValue) =
      M.product M.membership (M.product (M.meet M.stageValue M.domain) M.topValue) := by
    have middle : M.product M.domain (M.product M.stageValue M.topValue) =
        M.product (M.meet M.stageValue M.domain) M.topValue := by
      rw [← show M.product (M.product M.domain M.stageValue) M.topValue =
        M.product M.domain (M.product M.stageValue M.topValue) from laws.mul_assoc _ _ _,
        fuse, model.boolean.commutative M.domain]
    rw [show M.product (M.product M.membership M.domain) (M.product M.stageValue M.topValue) =
      M.product M.membership (M.product M.domain (M.product M.stageValue M.topValue)) from
        laws.mul_assoc _ _ _, middle]
  rwa [before] at law

/-- The shared membership and stage equations precede the three
older equations for the auxiliary local signature. -/
def ambientEquations : List PalomarI3380.Equation := Manifest.preceding.take 18

theorem ModelsOn.ambient (model : M.ModelsOn safe) (localRel : A → A) (node : A → A → A → A) :
    (M.relationAlgebra localRel node).Models ambientEquations := by
  let laws := model.relation_laws localRel node
  intro eq listed v
  simp only [ambientEquations, Manifest.preceding, Manifest.retained,
    List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
    List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst eq
  · exact (model.equations boolean_left (by simp [Templates.equations]) (v 0) (v 1) (v 2)
      M.seed model.seed_safe).symm
  · exact (model.equations boolean_right (by simp [Templates.equations]) (v 0) (v 1) (v 2)
      M.seed model.seed_safe).symm
  · rfl
  · exact congrArg (fun selector => M.product (M.converse selector) selector)
      (model.choice_subset_agrees).symm
  · exact model.associative _ _ _
  · exact laws.unit_right _
  · exact laws.conv_inv _
  · change M.meet (M.product (v 0) (v 1)) (M.product (v 0) (M.meet (v 2) (v 1))) = _
    have h := laws.mul_mono_right (model.boolean.inf_le_right (v 2) (v 1)) (v 0)
    exact (model.boolean.commutative _ _).trans h
  · exact laws.conv_inf _ _
  · exact laws.peirce_eq _ _
  · exact model.extensionality
  · exact model.maskedChoice_subset _
  · exact (model.boolean.disjoint_iff_le M.membership _ _).mpr (model.maskedChoice_function _)
  · exact model.maskedChoice_domain _
  · exact model.image_equation _
  · exact model.domain_equation.symm
  · change M.product M.stageValue (M.converse M.membership) =
      M.product (M.product (M.product M.stageValue (M.converse M.membership)) M.stageValue)
        (M.converse M.subsetValue)
    have same := congrArg M.converse model.stage_equation
    have transpose (x y : A) :
        M.converse (M.product x y) = M.product (M.converse y) (M.converse x) :=
      laws.conv_product x y
    have diagonal : M.converse M.stageValue = M.stageValue :=
      laws.unit_converse model.stage_subidentity
    simpa only [transpose, diagonal] using same.symm
  · change M.domain = M.meet M.identity
      (M.product (M.product M.membership (M.meet M.stageValue M.domain)) M.topValue)
    rw [show M.product (M.product M.membership (M.meet M.stageValue M.domain)) M.topValue =
      M.product M.membership (M.product (M.meet M.stageValue M.domain) M.topValue) from
        laws.mul_assoc _ _ _]
    exact model.domain_closed.symm

end PalomarI3334.NativeAlgebra
