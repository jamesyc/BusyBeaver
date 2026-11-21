module
public import I3_380.RelationAlgebra.Boolean
public import I3_380.Conservativity
@[expose] public section

namespace PalomarI3380

namespace Algebra

abbrev le {A : Type} (M : Algebra A) : A → A → Prop := MeredithLaws.Le M.inf
abbrev sup {A : Type} (M : Algebra A) : A → A → A := MeredithLaws.sup M.inf M.neg
abbrev top {A : Type} (M : Algebra A) : A := MeredithLaws.top M.inf M.neg (M.constant .I)
abbrev zero {A : Type} (M : Algebra A) : A := MeredithLaws.bottom M.inf M.neg (M.constant .I)

end Algebra

structure RelationLaws {A : Type} (M : Algebra A) : Prop where
  bool : MeredithLaws M.inf M.neg
  mul_assoc : ∀ x y z, M.product (M.product x y) z = M.product x (M.product y z)
  unit_right : ∀ x, M.product x (M.constant .I) = x
  conv_inv : ∀ x, M.converse (M.converse x) = x
  mul_mono_right : ∀ {x y}, M.le x y → ∀ a, M.le (M.product a x) (M.product a y)
  conv_inf : ∀ x y, M.converse (M.inf x y) = M.inf (M.converse x) (M.converse y)
  peirce_eq : ∀ x y,
    M.inf (M.product (M.converse x) (M.neg (M.product x y))) y = M.neg (M.constant .U)

namespace RelationLaws

open Manifest

private def valuation {A : Type} (x y z : A) : Fin 3 → A :=
  fun i => if i.val = 0 then x else if i.val = 1 then y else z

theorem of_model {A : Type} (M : Algebra A) (hM : M.Models preceding) : RelationLaws M := by
  have bool := meredithLaws M.inf M.neg
    (fun x y => hM meredith1 (by simp [preceding]) (valuation x y x))
    (fun x y z => hM meredith2 (by simp [preceding]) (valuation x y z))
  refine ⟨bool, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    exact (hM productAssociative (by simp [preceding, retained]) (valuation x y z)).symm
  · intro x
    exact hM rightIdentity (by simp [preceding, retained]) (valuation x x x)
  · intro x
    exact hM converseInvolution (by simp [preceding, retained]) (valuation x x x)
  · intro x y hxy a
    change M.inf x y = x at hxy
    have h := hM productMonotonicity (by simp [preceding, retained]) (valuation a y x)
    change M.inf (M.product a y) (M.product a (M.inf x y)) = M.product a (M.inf x y) at h
    rw [hxy, bool.commutative] at h
    exact h
  · intro x y
    exact hM converseMeet (by simp [preceding, retained]) (valuation x y x)
  · intro x y
    exact hM peirce (by simp [preceding, retained]) (valuation x y x)

variable {A : Type} {M : Algebra A} (L : RelationLaws M)
include L

theorem universal_top : M.constant .U = M.top := by
  have topEq := L.peirce_eq (M.constant .I) M.zero
  rw [L.bool.commutative, L.bool.bottom_meet] at topEq
  have h := congrArg M.neg topEq
  simp only [MeredithLaws.bottom, L.bool.involution] at h
  exact h.symm

theorem peirce_le (a b : A) :
    M.le (M.product (M.converse a) (M.neg (M.product a b))) (M.neg b) := by
  apply (L.bool.disjoint_iff_le (M.constant .I) _ _).mp
  rw [L.bool.involution, L.peirce_eq, L.universal_top]
  rfl

/-- The right residual follows from the literal monotonicity and Peirce laws. -/
theorem residual (a b c : A) :
    M.le (M.product a b) c ↔ M.le b (M.neg (M.product (M.converse a) (M.neg c))) := by
  constructor
  · intro h
    have hd := (L.bool.neg_order _ _).mpr h
    have hPeirce := L.bool.le_trans (L.mul_mono_right hd (M.converse a)) (L.peirce_le a b)
    apply (L.bool.neg_order _ _).mp
    simpa only [L.bool.involution] using hPeirce
  · intro h
    have peirce := L.peirce_le (M.converse a) (M.neg c)
    rw [L.conv_inv, L.bool.involution] at peirce
    exact L.bool.le_trans (L.mul_mono_right h a) peirce

theorem conv_mono {a b : A} (h : M.le a b) : M.le (M.converse a) (M.converse b) := by
  change M.inf a b = a at h
  change M.inf (M.converse a) (M.converse b) = M.converse a
  rw [← L.conv_inf, h]

/-- Converse reverses composition. Right residuals are unique, so the
residual of two consecutive multiplications is the reversed composition
of their residuals. The right unit then identifies the two converses. -/
theorem conv_product (a b : A) :
    M.converse (M.product a b) = M.product (M.converse b) (M.converse a) := by
  have same (x : A) :
      M.le x (M.neg (M.converse (M.product a b))) ↔
        M.le x (M.neg (M.product (M.converse b) (M.converse a))) := by
    let c := M.neg (M.constant .I)
    calc
      _ ↔ M.le x (M.neg (M.product (M.converse (M.product a b)) (M.neg c))) := by
        simp only [c, L.bool.involution, L.unit_right]
      _ ↔ M.le (M.product (M.product a b) x) c := (L.residual _ _ _).symm
      _ ↔ M.le (M.product a (M.product b x)) c := by rw [L.mul_assoc]
      _ ↔ M.le (M.product b x) (M.neg (M.product (M.converse a) (M.neg c))) := L.residual _ _ _
      _ ↔ M.le x (M.neg (M.product (M.converse b)
        (M.neg (M.neg (M.product (M.converse a) (M.neg c)))))) := L.residual _ _ _
      _ ↔ _ := by simp only [c, L.bool.involution, L.unit_right]
  have h := L.bool.le_antisymm ((same _).mp (L.bool.le_refl _)) ((same _).mpr (L.bool.le_refl _))
  have eq := congrArg M.neg h
  simpa only [L.bool.involution] using eq

theorem unit_left (a : A) : M.product (M.constant .I) a = a := by
  have left (b : A) : M.product (M.converse (M.constant .I)) b = b := by
    have h := congrArg M.converse (L.unit_right (M.converse b))
    simpa only [L.conv_product, L.conv_inv] using h
  have eq := (L.unit_right (M.converse (M.constant .I))).symm.trans (left (M.constant .I))
  rw [← eq]
  exact left a

theorem conv_unit : M.converse (M.constant .I) = M.constant .I := by
  have h := congrArg M.converse (L.unit_left (M.constant .I))
  rw [L.conv_product] at h
  have left (b : A) : M.product (M.converse (M.constant .I)) b = b := by
    have eq := congrArg M.converse (L.unit_right (M.converse b))
    simpa only [L.conv_product, L.conv_inv] using eq
  exact (L.unit_right _).symm.trans (left _)

theorem mul_mono_left {a b : A} (h : M.le a b) (c : A) :
    M.le (M.product a c) (M.product b c) := by
  have h' := L.conv_mono (L.mul_mono_right (L.conv_mono h) (M.converse c))
  simpa only [L.conv_product, L.conv_inv] using h'

theorem mul_zero (a : A) : M.product a M.zero = M.zero := by
  apply L.bool.le_antisymm
  · exact (L.residual _ _ _).mpr (L.bool.bottom_le _ _)
  · exact L.bool.bottom_le _ _

theorem conv_zero : M.converse M.zero = M.zero := by
  apply L.bool.le_antisymm
  · have h := L.conv_mono (L.bool.bottom_le (M.constant .I) (M.converse M.zero))
    simpa only [L.conv_inv] using h
  · exact L.bool.bottom_le _ _

theorem zero_mul (a : A) : M.product M.zero a = M.zero := by
  have h := congrArg M.converse (L.mul_zero (M.converse a))
  simpa only [L.conv_product, L.conv_inv, L.conv_zero] using h

theorem mul_sup_right (a b c : A) :
    M.product a (M.sup b c) = M.sup (M.product a b) (M.product a c) := by
  have adj (d : A) : M.le (M.product a (M.sup b c)) d ↔
      M.le (M.sup (M.product a b) (M.product a c)) d := by
    calc
      _ ↔ M.le (M.sup b c) (M.neg (M.product (M.converse a) (M.neg d))) :=
        L.residual _ _ _
      _ ↔ M.le b (M.neg (M.product (M.converse a) (M.neg d))) ∧
          M.le c (M.neg (M.product (M.converse a) (M.neg d))) := L.bool.sup_le
      _ ↔ M.le (M.product a b) d ∧ M.le (M.product a c) d :=
        and_congr (L.residual _ _ _).symm (L.residual _ _ _).symm
      _ ↔ _ := L.bool.sup_le.symm
  exact L.bool.le_antisymm ((adj _).mpr (L.bool.le_refl _)) ((adj _).mp (L.bool.le_refl _))

theorem conv_sup (a b : A) :
    M.converse (M.sup a b) = M.sup (M.converse a) (M.converse b) := by
  apply L.bool.le_antisymm
  · have h : M.le (M.sup a b) (M.converse (M.sup (M.converse a) (M.converse b))) := by
      apply L.bool.sup_le.mpr
      constructor
      · have hx := L.conv_mono (L.bool.le_sup_left (M.converse a) (M.converse b))
        simpa only [L.conv_inv] using hx
      · have hx := L.conv_mono (L.bool.le_sup_right (M.converse a) (M.converse b))
        simpa only [L.conv_inv] using hx
    simpa only [L.conv_inv] using L.conv_mono h
  · exact L.bool.sup_le.mpr ⟨L.conv_mono (L.bool.le_sup_left a b),
      L.conv_mono (L.bool.le_sup_right a b)⟩

theorem conv_neg (a : A) : M.converse (M.neg a) = M.neg (M.converse a) := by
  have below (x : A) : M.le (M.converse (M.neg x)) (M.neg (M.converse x)) := by
    apply (L.bool.disjoint_iff_le (M.constant .I) _ _).mp
    rw [L.bool.involution, ← L.conv_inf, L.bool.commutative (M.neg x) x, L.bool.inf_complement, L.conv_zero]
  apply L.bool.le_antisymm (below a)
  have h := L.conv_mono (below (M.converse a))
  simpa only [L.conv_inv] using h

theorem conv_top : M.converse M.top = M.top := by
  have eq : M.neg M.zero = M.top := L.bool.involution _
  rw [← eq, L.conv_neg, L.conv_zero]

theorem mul_sup_left (a b c : A) :
    M.product (M.sup a b) c = M.sup (M.product a c) (M.product b c) := by
  have eq := congrArg M.converse (L.mul_sup_right (M.converse c) (M.converse a) (M.converse b))
  simpa only [L.conv_product, L.conv_sup, L.conv_inv] using eq

/-- The adjunction expressed as the cycle law for disjointness. -/
theorem cycle (a b c : A) :
    M.inf (M.product a b) c = M.zero ↔ M.inf b (M.product (M.converse a) c) = M.zero := by
  calc
    _ ↔ M.le (M.product a b) (M.neg c) := by
      simpa only [L.bool.involution] using L.bool.disjoint_iff_le (M.constant .I) (M.product a b) (M.neg c)
    _ ↔ M.le b (M.neg (M.product (M.converse a) (M.neg (M.neg c)))) := L.residual _ _ _
    _ ↔ _ := by
      simp only [L.bool.involution]
      simpa only [L.bool.involution] using
        (L.bool.disjoint_iff_le (M.constant .I) b (M.neg (M.product (M.converse a) c))).symm

end RelationLaws
end PalomarI3380
