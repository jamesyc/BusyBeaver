module
public import I3_334Support.RelationAlgebra.Laws
public import I3_334Support.SetTheory.Graphs.NamedPoints
@[expose] public section

namespace PalomarI3380.RelationLaws

variable {A : Type} {M : Algebra A} (L : RelationLaws M)
include L

theorem le_zero_iff (x : A) : M.le x M.zero ↔ x = M.zero :=
  ⟨fun h => L.bool.le_antisymm h (L.bool.bottom_le _ _), fun h => h ▸ L.bool.le_refl _⟩

theorem inf_under_complement {x a : A} (le₁ : M.le x a) (le₂ : M.le x (M.neg a)) :
    x = M.zero := by
  have both := L.bool.le_inf.mpr ⟨le₁, le₂⟩
  rw [L.bool.inf_complement (M.constant .I) a] at both
  exact (L.le_zero_iff _).mp both

theorem inf_left_exchange (a b c : A) : M.inf a (M.inf b c) = M.inf b (M.inf a c) := by
  rw [← L.bool.associative, L.bool.commutative a b, L.bool.associative]

theorem neg_zero : M.neg M.zero = M.top := L.bool.involution _

theorem unit_product_le {e f : A} (he : M.le e (M.constant .I)) (hf : M.le f (M.constant .I)) :
    M.le (M.product e f) (M.inf e f) := by
  have left := L.mul_mono_right hf e
  have right := L.mul_mono_left he f
  rw [L.unit_right] at left
  rw [L.unit_left] at right
  exact L.bool.le_inf.mpr ⟨left, right⟩

/-- Subidentities multiply by intersection. -/
theorem unit_product {e f : A} (he : M.le e (M.constant .I)) (hf : M.le f (M.constant .I)) :
    M.product e f = M.inf e f := by
  have idempotent {x : A} (hx : M.le x (M.constant .I)) : M.product x x = x := by
    let complement := M.inf (M.constant .I) (M.neg x)
    have eqSup : M.sup x complement = M.constant .I :=
      L.bool.relative_complement (M.constant .I) x (M.constant .I) hx
    have hComp : M.le complement (M.constant .I) := L.bool.inf_le_left _ _
    have zero : M.product x complement = M.zero := by
      have both := L.unit_product_le hx hComp
      exact L.inf_under_complement
        (L.bool.le_trans both (L.bool.inf_le_left _ _))
        (L.bool.le_trans both (L.bool.le_trans (L.bool.inf_le_right _ _) (L.bool.inf_le_right _ _)))
    have h := L.mul_sup_right x x complement
    have hs : M.sup (M.product x x) M.zero = M.product x x := L.bool.sup_bottom _ _
    rw [eqSup, L.unit_right, zero, hs] at h
    exact h.symm
  apply L.bool.le_antisymm (L.unit_product_le he hf)
  have meetSubunit : M.le (M.inf e f) (M.constant .I) :=
    L.bool.le_trans (L.bool.inf_le_left e f) he
  have eProd := L.mul_mono_left (L.bool.inf_le_left e f) (M.inf e f)
  have fProd := L.mul_mono_right (L.bool.inf_le_right e f) e
  have joint := L.bool.le_trans eProd fProd
  rwa [idempotent meetSubunit] at joint

theorem unit_converse {e : A} (he : M.le e (M.constant .I)) : M.converse e = e := by
  have direction (f : A) (hf : M.le f (M.constant .I)) : M.le (M.converse f) f := by
    let c := M.inf (M.constant .I) (M.neg f)
    have hc : M.le c (M.constant .I) := L.bool.inf_le_left _ _
    have hCv := L.conv_mono hf
    rw [L.conv_unit] at hCv
    have peirce := L.peirce_le f (M.constant .I)
    rw [L.unit_right] at peirce
    have narrow := L.mul_mono_right (L.bool.inf_le_right (M.constant .I) (M.neg f)) (M.converse f)
    have below := L.bool.le_trans narrow peirce
    change M.le (M.product (M.converse f) c) (M.neg (M.constant .I)) at below
    have bounded := L.bool.le_trans (L.unit_product_le hCv hc)
      (L.bool.le_trans (L.bool.inf_le_right _ _) hc)
    have hZero := L.inf_under_complement bounded below
    rw [L.unit_product hCv hc] at hZero
    change M.inf (M.converse f) (M.inf (M.constant .I) (M.neg f)) = M.zero at hZero
    rw [← L.bool.associative, show M.inf (M.converse f) (M.constant .I) = M.converse f from hCv] at hZero
    exact (L.bool.disjoint_iff_le (M.constant .I) _ _).mp hZero
  apply L.bool.le_antisymm (direction e he)
  have hCv := L.conv_mono he
  rw [L.conv_unit] at hCv
  have h := direction (M.converse e) hCv
  rwa [L.conv_inv] at h

/-- Restricting a relation on the left by a subidentity restricts its domain. -/
theorem restrict_left {e : A} (he : M.le e (M.constant .I)) (r : A) :
    M.product e r = M.inf r (M.product e M.top) := by
  let f := M.inf (M.constant .I) (M.neg e)
  have hf : M.le f (M.constant .I) := L.bool.inf_le_left _ _
  have both : M.sup e f = M.constant .I :=
    L.bool.relative_complement (M.constant .I) e (M.constant .I) he
  have hOrthogonal : M.product e f = M.zero := by
    rw [L.unit_product he hf]
    exact L.inf_under_complement (L.bool.inf_le_left _ _)
      (L.bool.le_trans (L.bool.inf_le_right _ _) (L.bool.inf_le_right _ _))
  have separated : M.inf (M.product e M.top) (M.product f M.top) = M.zero := by
    apply (L.cycle _ _ _).mpr
    rw [L.unit_converse he, ← L.mul_assoc, hOrthogonal, L.zero_mul,
      L.bool.commutative M.top M.zero, L.bool.bottom_meet]
  have partZero : M.inf (M.product e M.top) (M.product f r) = M.zero := by
    apply (L.le_zero_iff _).mp
    have h := L.bool.inf_mono (L.bool.le_refl (M.product e M.top))
      (L.mul_mono_right (L.bool.le_top (M.constant .I) r) f)
    rwa [separated] at h
  have decomposed := L.mul_sup_left e f r
  rw [both, L.unit_left] at decomposed
  have same := L.mul_mono_right (L.bool.le_top (M.constant .I) r) e
  calc
    M.product e r = M.sup (M.product e r) M.zero := (L.bool.sup_bottom _ _).symm
    _ = M.inf (M.product e M.top) (M.sup (M.product e r) (M.product f r)) := by
        rw [L.bool.inf_sup (M.constant .I), partZero, L.bool.commutative (M.product e M.top) (M.product e r),
          show M.inf (M.product e r) (M.product e M.top) = M.product e r from same]
    _ = M.inf r (M.product e M.top) := by rw [← decomposed, L.bool.commutative]

theorem restrict_right {e : A} (he : M.le e (M.constant .I)) (r : A) :
    M.product r e = M.inf r (M.product M.top e) := by
  have h := congrArg M.converse (L.restrict_left he (M.converse r))
  simpa only [L.conv_product, L.conv_inf, L.conv_inv, L.unit_converse he, L.conv_top] using h

def support (M : Algebra A) (r : A) : A :=
  M.inf (M.constant .I) (M.product r M.top)

omit L in
theorem support_subunit (B : MeredithLaws M.inf M.neg) (r : A) :
    M.le (support M r) (M.constant .I) := B.inf_le_left _ _

theorem support_mono {a b : A} (h : M.le a b) : M.le (support M a) (support M b) :=
  L.bool.inf_mono (L.bool.le_refl _) (L.mul_mono_left h _)

theorem probe_zero {e : A} (he : M.le e (M.constant .I)) (a : A) :
    M.product e a = M.zero ↔ M.inf e (support M a) = M.zero := by
  have flip : M.product e a = M.zero ↔ M.product (M.converse a) e = M.zero := by
    constructor
    · intro h
      simpa only [L.conv_product, L.unit_converse he, L.conv_zero] using congrArg M.converse h
    · intro h
      simpa only [L.conv_product, L.unit_converse he, L.conv_inv, L.conv_zero] using congrArg M.converse h
  rw [flip, ← L.le_zero_iff, L.residual, L.conv_inv, L.neg_zero]
  have disjoint := L.bool.disjoint_iff_le (M.constant .I) e (M.neg (M.product a M.top))
  rw [L.bool.involution] at disjoint
  refine disjoint.symm.trans ?_
  simp only [support, ← L.bool.associative, show M.inf e (M.constant .I) = e from he]

theorem support_restrict {e : A} (he : M.le e (M.constant .I)) (r : A) :
    support M (M.product e r) = M.inf e (support M r) := by
  have eSupport : support M e = e := by
    have h := L.restrict_left he (M.constant .I)
    rw [L.unit_right] at h
    exact h.symm
  unfold support
  rw [L.mul_assoc, L.restrict_left he, L.bool.commutative (M.product r M.top) (M.product e M.top),
    ← L.bool.associative, show M.inf (M.constant .I) (M.product e M.top) = e from eSupport,
    ← L.bool.associative, show M.inf e (M.constant .I) = e from he]

theorem support_unit {e : A} (he : M.le e (M.constant .I)) : support M e = e := by
  have h := (L.restrict_left he (M.constant .I)).symm
  rwa [L.unit_right] at h

theorem probe_equality {a b : A} (ha : M.le a (M.constant .I)) (hb : M.le b (M.constant .I))
    (same : ∀ e, M.le e (M.constant .I) → (M.inf e a = M.zero ↔ M.inf e b = M.zero)) :
    a = b := by
  have below (x y : A) (hx : M.le x (M.constant .I))
      (test : M.inf (M.inf (M.constant .I) (M.neg y)) x = M.zero) : M.le x y := by
    rw [L.bool.commutative _ x, ← L.bool.associative, show M.inf x (M.constant .I) = x from hx] at test
    exact (L.bool.disjoint_iff_le (M.constant .I) x y).mp test
  have probe (x : A) : M.inf (M.inf (M.constant .I) (M.neg x)) x = M.zero := by
    rw [L.bool.associative, L.bool.commutative (M.neg x) x, L.bool.inf_complement,
      L.bool.commutative (M.constant .I) M.zero, L.bool.bottom_meet]
  apply L.bool.le_antisymm
  · exact below a b ha ((same _ (L.bool.inf_le_left _ _)).mpr (probe b))
  · exact below b a hb ((same _ (L.bool.inf_le_left _ _)).mp (probe a))

theorem support_inf (a b : A) :
    support M (M.inf a b) = M.inf (M.constant .I) (M.product a (M.converse b)) := by
  apply L.probe_equality (support_subunit L.bool _) (L.bool.inf_le_left _ _)
  intro e he
  rw [← L.probe_zero he, ← L.bool.associative,
    show M.inf e (M.constant .I) = e from he,
    L.bool.commutative e (M.product a (M.converse b)), L.cycle]
  have matchEq : M.inf (M.converse b) (M.product (M.converse a) e) = M.zero ↔
      M.inf b (M.product e a) = M.zero := by
    constructor <;> intro h
    · have eq := congrArg M.converse h
      simpa only [L.conv_zero, L.conv_inf, L.conv_product, L.conv_inv, L.unit_converse he] using eq
    · have eq := congrArg M.converse h
      simpa only [L.conv_zero, L.conv_inf, L.conv_product, L.conv_inv, L.unit_converse he] using eq
  rw [matchEq, L.restrict_left he a, L.restrict_left he (M.inf a b),
    ← L.bool.associative, L.bool.commutative b a]

theorem support_self (r : A) :
    support M r = M.inf (M.constant .I) (M.product r (M.converse r)) := by
  have h := L.support_inf r r
  rwa [L.bool.idempotent] at h

theorem support_apply (r : A) : M.product (support M r) r = r := by
  let d := support M r
  let f := M.inf (M.constant .I) (M.neg d)
  have hd : M.le d (M.constant .I) := support_subunit L.bool r
  have hf : M.le f (M.constant .I) := L.bool.inf_le_left _ _
  have eq := L.mul_sup_left d f r
  have hSup : M.sup d f = M.constant .I := L.bool.relative_complement (M.constant .I) _ _ hd
  rw [hSup, L.unit_left] at eq
  have fZero : M.product f r = M.zero := by
    apply (L.probe_zero hf r).mpr
    change M.inf (M.inf (M.constant .I) (M.neg d)) d = M.zero
    rw [L.bool.associative, L.bool.commutative (M.neg d) d, L.bool.inf_complement,
      L.bool.commutative (M.constant .I) M.zero, L.bool.bottom_meet]
  have hs : M.sup (M.product d r) M.zero = M.product d r := L.bool.sup_bottom _ _
  rw [fZero, hs] at eq
  exact eq.symm

theorem support_top (r : A) : M.product r M.top = M.product (support M r) M.top := by
  apply L.bool.le_antisymm
  · have h := L.mul_mono_right (L.bool.le_top (M.constant .I) (M.product r M.top)) (support M r)
    rw [← L.mul_assoc, L.support_apply] at h
    exact h
  · rw [L.support_self]
    exact L.bool.le_trans
      (L.mul_mono_left (L.bool.inf_le_right _ _) M.top)
      (by rw [L.mul_assoc]; exact L.mul_mono_right (L.bool.le_top _ _) r)

theorem support_nonzero {r : A} (h : r ≠ M.zero) : support M r ≠ M.zero := by
  intro eq
  have hRun := L.support_apply r
  rw [eq, L.zero_mul] at hRun
  exact h hRun.symm

end PalomarI3380.RelationLaws
