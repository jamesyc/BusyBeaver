module
public import I3_334Support.RelationAlgebra.Functional
@[expose] public section

namespace PalomarI3380.RelationLaws

open Manifest

variable {A : Type} {M : Algebra A} (L : RelationLaws M)

/-- The subidentity on which the values of `f` and `g` are related by `r`. -/
def witness (M : Algebra A) (r f g : A) : A :=
  M.inf (M.constant .I) (M.product (M.product f r) (M.converse g))

include L

theorem witness_subunit (r f g : A) : M.le (witness M r f g) (M.constant .I) :=
  L.bool.inf_le_left _ _

theorem witness_mono {r s : A} (hle : M.le r s) (f g : A) :
    M.le (witness M r f g) (witness M s f g) :=
  L.bool.inf_mono (L.bool.le_refl _) (L.mul_mono_left (L.mul_mono_right hle f) _)

theorem witness_unit (f g : A) :
    witness M (M.constant .I) f g = support M (M.inf f g) := by
  rw [witness, L.unit_right, L.support_inf]

theorem witness_converse (r f g : A) : witness M (M.converse r) f g = witness M r g f := by
  have h := L.unit_converse (L.witness_subunit r g f)
  change M.converse (M.inf (M.constant .I) (M.product (M.product g r) (M.converse f))) = _ at h
  simp only [L.conv_inf, L.conv_unit, L.conv_product, L.conv_inv, ← L.mul_assoc] at h
  exact h

theorem witness_zero (f g : A) : witness M M.zero f g = M.zero := by
  rw [witness, L.mul_zero, L.zero_mul, L.bool.commutative (M.constant .I) M.zero, L.bool.bottom_meet]

private theorem witness_restrict_both {e f : A}
    (he : M.le e (M.constant .I)) (hf : M.le f (M.constant .I)) (r : A) :
    M.inf (M.constant .I) (M.product (M.product e r) f) =
      M.inf (M.inf e f) (M.inf (M.constant .I) r) := by
  rw [L.restrict_right hf, L.restrict_left he]
  have supportE : M.inf (M.constant .I) (M.product e M.top) = e := L.support_unit he
  have supportF : M.inf (M.constant .I) (M.product M.top f) = f := by
    have h := L.restrict_right hf (M.constant .I)
    rw [L.unit_left] at h
    exact h.symm
  let x := M.inf (M.constant .I) (M.inf (M.inf r (M.product e M.top)) (M.product M.top f))
  let y := M.inf (M.inf e f) (M.inf (M.constant .I) r)
  apply L.bool.le_antisymm
  · change M.le x y
    have xI : M.le x (M.constant .I) := L.bool.inf_le_left _ _
    have xInner : M.le x (M.inf (M.inf r (M.product e M.top)) (M.product M.top f)) :=
      L.bool.inf_le_right _ _
    have xMeets : M.le x (M.inf r (M.product e M.top)) := L.bool.le_trans xInner (L.bool.inf_le_left _ _)
    have xe : M.le x e := by
      rw [← supportE]
      exact L.bool.le_inf.mpr ⟨xI, L.bool.le_trans xMeets (L.bool.inf_le_right _ _)⟩
    have xf : M.le x f := by
      rw [← supportF]
      exact L.bool.le_inf.mpr ⟨xI, L.bool.le_trans xInner (L.bool.inf_le_right _ _)⟩
    exact L.bool.le_inf.mpr ⟨L.bool.le_inf.mpr ⟨xe, xf⟩,
      L.bool.le_inf.mpr ⟨xI, L.bool.le_trans xMeets (L.bool.inf_le_left _ _)⟩⟩
  · change M.le y x
    have yMeet : M.le y (M.inf e f) := L.bool.inf_le_left _ _
    have yParts : M.le y (M.inf (M.constant .I) r) := L.bool.inf_le_right _ _
    have eTop : M.le e (M.product e M.top) := by
      have eq := L.mul_mono_right (L.bool.le_top (M.constant .I) (M.constant .I)) e
      rwa [L.unit_right] at eq
    have fTop : M.le f (M.product M.top f) := by
      have eq := L.mul_mono_left (L.bool.le_top (M.constant .I) (M.constant .I)) f
      rwa [L.unit_left] at eq
    exact L.bool.le_inf.mpr ⟨L.bool.le_trans yParts (L.bool.inf_le_left _ _),
      L.bool.le_inf.mpr ⟨
        L.bool.le_inf.mpr ⟨L.bool.le_trans yParts (L.bool.inf_le_right _ _),
          L.bool.le_trans yMeet (L.bool.le_trans (L.bool.inf_le_left _ _) eTop)⟩,
        L.bool.le_trans yMeet (L.bool.le_trans (L.bool.inf_le_right _ _) fTop)⟩⟩

theorem witness_restrict {e : A} (he : M.le e (M.constant .I)) (r f g : A) :
    witness M r (M.product e f) (M.product e g) = M.inf e (witness M r f g) := by
  unfold witness
  have eq :
      M.product (M.product (M.product e f) r) (M.converse (M.product e g)) =
        M.product (M.product e (M.product (M.product f r) (M.converse g))) e := by
    simp only [L.conv_product, L.unit_converse he, L.mul_assoc]
  rw [eq, L.witness_restrict_both he he, L.bool.idempotent]

theorem witness_top (f g : A) :
    witness M M.top f g = M.inf (support M f) (support M g) := by
  have hRight : M.product M.top (M.converse g) = M.product M.top (support M g) := by
    have h := congrArg M.converse (L.support_top g)
    simpa only [L.conv_product, L.conv_top, L.unit_converse (support_subunit L.bool g)] using h
  unfold witness
  rw [L.mul_assoc, hRight, ← L.mul_assoc, L.support_top f,
    L.witness_restrict_both (support_subunit L.bool f) (support_subunit L.bool g),
    show M.inf (M.constant .I) M.top = M.constant .I from L.bool.le_top _ _]
  exact L.bool.le_trans (L.bool.inf_le_left _ _) (support_subunit L.bool f)

theorem witness_inf {f g : A} (hf : Functional M f) (hg : Functional M g) (r s : A) :
    witness M (M.inf r s) f g = M.inf (witness M r f g) (witness M s f g) := by
  have infFactor (a b : A) :
      M.inf (M.constant .I) (M.inf a b) =
        M.inf (M.inf (M.constant .I) a) (M.inf (M.constant .I) b) := by
    rw [L.bool.associative, L.inf_left_exchange a (M.constant .I),
      ← L.bool.associative (M.constant .I) (M.constant .I), L.bool.idempotent]
  rw [witness, L.functional_mul_inf hf, L.functional_inf_mul_converse hg, infFactor]
  rfl

theorem witness_sup (r s f g : A) :
    witness M (M.sup r s) f g = M.sup (witness M r f g) (witness M s f g) := by
  rw [witness, L.mul_sup_right, L.mul_sup_left, L.bool.inf_sup (M.constant .I)]
  rfl

theorem witness_compose {f g h : A} (hh : Functional M h) (r s : A) :
    M.le (M.inf (witness M r f h) (witness M s h g)) (witness M (M.product r s) f g) := by
  let e := M.inf (witness M r f h) (witness M s h g)
  have he : M.le e (M.constant .I) := L.bool.le_trans (L.bool.inf_le_left _ _) (L.witness_subunit _ _ _)
  have hE : M.product e e = e := (L.unit_product he he).trans (L.bool.idempotent _)
  have first : M.le e (M.product (M.product f r) (M.converse h)) :=
    L.bool.le_trans (L.bool.inf_le_left _ _) (L.bool.inf_le_right _ _)
  have second : M.le e (M.product (M.product h s) (M.converse g)) :=
    L.bool.le_trans (L.bool.inf_le_right _ _) (L.bool.inf_le_right _ _)
  have fused := L.bool.le_trans (L.mul_mono_left first e) (L.mul_mono_right second _)
  rw [hE] at fused
  have bound := L.mul_mono_left (L.mul_mono_right hh (M.product f r)) (M.product s (M.converse g))
  rw [L.unit_right] at bound
  let middle := M.product f (M.product r (M.product (M.converse h) (M.product h (M.product s (M.converse g)))))
  have hFirst : M.le e middle := by simpa only [L.mul_assoc, middle] using fused
  have hSecond : M.le middle (M.product (M.product f (M.product r s)) (M.converse g)) := by
    simpa only [L.mul_assoc, middle] using bound
  exact L.bool.le_inf.mpr ⟨he, L.bool.le_trans hFirst hSecond⟩

/-- The selected intermediate function realizes the full support of a
composed edge. This is the use of the literal selector's domain equation. -/
theorem witness_intermediate (hM : M.Models preceding) (r s f g : A) :
    ∃ h, Functional M h ∧ support M h = witness M (M.product r s) f g ∧
      M.le (support M h) (witness M r f h) ∧ M.le (support M h) (witness M s h g) := by
  let t := M.inf (M.product f r) (M.product g (M.converse s))
  let h := M.choice t
  have left : M.le h (M.product f r) :=
    L.bool.le_trans (choice_subalgebra hM t) (L.bool.inf_le_left _ _)
  have right : M.le h (M.product g (M.converse s)) :=
    L.bool.le_trans (choice_subalgebra hM t) (L.bool.inf_le_right _ _)
  refine ⟨h, L.choice_function hM t, ?_, ?_, ?_⟩
  · change support M (M.choice t) = _
    rw [L.choice_support hM]
    unfold t witness
    rw [L.support_inf, L.conv_product, L.conv_inv]
    simp only [L.mul_assoc]
  · rw [L.support_self h]
    exact L.bool.inf_mono (L.bool.le_refl _) (L.mul_mono_left left _)
  · rw [L.support_self h]
    have bound := L.conv_mono right
    rw [L.conv_product, L.conv_inv] at bound
    have eq := L.mul_mono_right bound h
    rw [← L.mul_assoc] at eq
    exact L.bool.inf_mono (L.bool.le_refl _) eq

end PalomarI3380.RelationLaws
