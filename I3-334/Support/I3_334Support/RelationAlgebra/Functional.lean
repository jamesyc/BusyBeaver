module
public import I3_334Support.RelationAlgebra.Domain
@[expose] public section

namespace PalomarI3380.RelationLaws

open Manifest

variable {A : Type} {M : Algebra A} (L : RelationLaws M)

def Functional (M : Algebra A) (r : A) : Prop :=
  M.le (M.product (M.converse r) r) (M.constant .I)

include L

theorem functional_mono {f r : A} (h : M.le r f) (hf : Functional M f) : Functional M r :=
  L.bool.le_trans
    (L.bool.le_trans (L.mul_mono_left (L.conv_mono h) r) (L.mul_mono_right h (M.converse f))) hf

omit L in
theorem choice_subalgebra (hM : M.Models preceding) (r : A) : M.le (M.choice r) r :=
  hM choiceSub (by simp [preceding, retained]) (fun _ => r)

theorem choice_function (hM : M.Models preceding) (r : A) : Functional M (M.choice r) := by
  apply (L.bool.disjoint_iff_le (M.constant .I) _ _).mp
  have h := hM choiceFunctional (by simp [preceding, retained]) (fun _ => r)
  change M.inf (M.product (M.converse (M.choice r)) (M.choice r)) (M.neg (M.constant .I)) =
    M.neg (M.constant .U) at h
  rw [L.universal_top] at h
  exact h

theorem choice_support (hM : M.Models preceding) (r : A) : support M (M.choice r) = support M r := by
  have h := hM choiceDomain (by simp [preceding, retained]) (fun _ => r)
  change M.product (M.choice r) (M.constant .U) = M.product r (M.constant .U) at h
  rw [L.universal_top] at h
  exact congrArg (M.inf (M.constant .I)) h

theorem identity_functional : Functional M (M.constant .I) := by
  unfold Functional
  rw [L.conv_unit, L.unit_right]
  exact L.bool.le_refl _

/-- A subrelation of a function with the same domain is the function. -/
theorem functional_eq_of_support {f r : A} (hf : Functional M f)
    (hLess : M.le r f) (hSame : support M r = support M f) : r = f := by
  apply L.bool.le_antisymm hLess
  have hFirst := L.mul_mono_left
    (L.bool.inf_le_right (M.constant .I) (M.product r (M.converse r))) f
  rw [← L.support_self r, hSame, L.support_apply, L.mul_assoc] at hFirst
  have hSecond : M.le (M.product (M.converse r) f) (M.constant .I) :=
    L.bool.le_trans (L.mul_mono_left (L.conv_mono hLess) f) hf
  have hThird := L.mul_mono_right hSecond r
  rw [L.unit_right] at hThird
  exact L.bool.le_trans hFirst hThird

theorem agreement_restrict {f g e : A} (hf : Functional M f) (hg : Functional M g)
    (he : M.le e (M.constant .I)) (h : M.le e (support M (M.inf f g))) :
    M.product e f = M.product e g := by
  let both := M.product e (M.inf f g)
  have hBoth : support M both = e := by
    change support M (M.product e (M.inf f g)) = e
    rw [L.support_restrict he]
    exact h
  have leftSupport : support M (M.product e f) = e := by
    rw [L.support_restrict he]
    exact L.bool.le_trans h (L.support_mono (L.bool.inf_le_left _ _))
  have rightSupport : support M (M.product e g) = e := by
    rw [L.support_restrict he]
    exact L.bool.le_trans h (L.support_mono (L.bool.inf_le_right _ _))
  have leftFun : Functional M (M.product e f) := by
    have smaller := L.mul_mono_left he f
    rw [L.unit_left] at smaller
    exact L.functional_mono smaller hf
  have rightFun : Functional M (M.product e g) := by
    have smaller := L.mul_mono_left he g
    rw [L.unit_left] at smaller
    exact L.functional_mono smaller hg
  have left := L.functional_eq_of_support leftFun
    (L.mul_mono_right (L.bool.inf_le_left f g) e) (hBoth.trans leftSupport.symm)
  have right := L.functional_eq_of_support rightFun
    (L.mul_mono_right (L.bool.inf_le_right f g) e) (hBoth.trans rightSupport.symm)
  exact left.symm.trans right

theorem restrict_agreement {f g e : A} (he : M.le e (M.constant .I))
    (defined : M.le e (support M f)) (eq : M.product e f = M.product e g) :
    M.le e (support M (M.inf f g)) := by
  have left := L.mul_mono_left he f
  have right := L.mul_mono_left he g
  rw [L.unit_left] at left right
  have both := L.bool.le_inf.mpr ⟨left, eq.symm ▸ right⟩
  have h := L.support_mono both
  rw [L.support_restrict he, show M.inf e (support M f) = e from defined] at h
  exact h

/-- Composition by a function on the left preserves intersections. -/
theorem functional_mul_inf {f : A} (hf : Functional M f) (a b : A) :
    M.product f (M.inf a b) = M.inf (M.product f a) (M.product f b) := by
  apply L.bool.le_antisymm
  · exact L.bool.le_inf.mpr ⟨L.mul_mono_right (L.bool.inf_le_left _ _) f,
      L.mul_mono_right (L.bool.inf_le_right _ _) f⟩
  · let t := M.inf (M.product f a) (M.product f b)
    let d := support M f
    have hd : M.le d (M.constant .I) := support_subunit L.bool f
    have onDomain : M.le t (M.product d M.top) := by
      rw [← L.support_top]
      exact L.bool.le_trans (L.bool.inf_le_left _ _) (L.mul_mono_right (L.bool.le_top _ _) f)
    have restrict : M.product d t = t := by
      rw [L.restrict_left hd]
      exact onDomain
    have domainLower : M.le d (M.product f (M.converse f)) := by
      change M.le (support M f) _
      rw [L.support_self]
      exact L.bool.inf_le_right _ _
    have expand := L.mul_mono_left domainLower t
    rw [restrict, L.mul_assoc] at expand
    have pullLeft : M.le (M.product (M.converse f) t) a := by
      have h := L.mul_mono_right (L.bool.inf_le_left (M.product f a) (M.product f b)) (M.converse f)
      rw [← L.mul_assoc] at h
      have lift := L.mul_mono_left hf a
      rw [L.unit_left] at lift
      exact L.bool.le_trans h lift
    have pullRight : M.le (M.product (M.converse f) t) b := by
      have h := L.mul_mono_right (L.bool.inf_le_right (M.product f a) (M.product f b)) (M.converse f)
      rw [← L.mul_assoc] at h
      have lift := L.mul_mono_left hf b
      rw [L.unit_left] at lift
      exact L.bool.le_trans h lift
    exact L.bool.le_trans expand (L.mul_mono_right (L.bool.le_inf.mpr ⟨pullLeft, pullRight⟩) f)

theorem functional_inf_mul_converse {f : A} (hf : Functional M f) (a b : A) :
    M.product (M.inf a b) (M.converse f) =
      M.inf (M.product a (M.converse f)) (M.product b (M.converse f)) := by
  have h := congrArg M.converse (L.functional_mul_inf hf (M.converse a) (M.converse b))
  simpa only [L.conv_product, L.conv_inf, L.conv_inv] using h

end PalomarI3380.RelationLaws
