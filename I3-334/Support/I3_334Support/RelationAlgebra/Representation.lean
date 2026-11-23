module
public import I3_334Support.RelationAlgebra.Witness
public import I3_334Support.RelationAlgebra.Ultrafilter
public import I3_334Support.SetTheory.Square.SquareProjections
@[expose] public section

namespace PalomarI3380.SubidentityUltrafilter

open RelationLaws Manifest

variable {A : Type} {M : Algebra A} (L : RelationLaws M) (F : SubidentityUltrafilter M)

def LocalFunction (F : SubidentityUltrafilter M) : Type :=
  { f : A // Functional M f ∧ F.member (support M f) }

/-- Two functions have the same value on an ultrafilter member. -/
def agrees (F : SubidentityUltrafilter M) (f g : LocalFunction F) : Prop :=
  F.member (support M (M.inf f.val g.val))

def functions (L : RelationLaws M) (F : SubidentityUltrafilter M) : Setoid (LocalFunction F) where
  r := agrees F
  iseqv := {
    refl := fun f => by
      unfold agrees
      rw [L.bool.idempotent]
      exact f.property.2
    symm := fun {f g} h => by
      unfold agrees at h ⊢
      rwa [L.bool.commutative]
    trans := fun {f g h} fg gh => by
      let left := support M (M.inf f.val g.val)
      let right := support M (M.inf g.val h.val)
      let e := M.inf left right
      have em : F.member e := F.filter_inf fg gh
      have he := F.subunit em
      have eq1 := L.agreement_restrict f.property.1 g.property.1 he (L.bool.inf_le_left left right)
      have eq2 := L.agreement_restrict g.property.1 h.property.1 he (L.bool.inf_le_right left right)
      have definedF := L.bool.le_trans (L.bool.inf_le_left left right)
        (L.support_mono (L.bool.inf_le_left f.val g.val))
      exact F.filter_up em (L.restrict_agreement he definedF (eq1.trans eq2))
        (support_subunit L.bool _)
  }

abbrev Points := Quotient (functions L F)

abbrev point (f : LocalFunction F) : Points L F := Quotient.mk (functions L F) f

def rawRel (F : SubidentityUltrafilter M) (r : A) (f g : LocalFunction F) : Prop :=
  F.member (witness M r f.val g.val)

include L in
private theorem witness_mem_restrict {e : A} (he : F.member e) (r f g : A) :
    F.member (witness M r (M.product e f) (M.product e g)) ↔ F.member (witness M r f g) := by
  rw [L.witness_restrict (F.subunit he)]
  exact ⟨fun m => F.filter_up m (L.bool.inf_le_right _ _) (L.witness_subunit _ _ _),
    fun m => F.filter_inf he m⟩

include L in
theorem rawRel_congr (r : A) {f f' g g' : LocalFunction F}
    (eqF : agrees F f f') (eqG : agrees F g g') :
    rawRel F r f g ↔ rawRel F r f' g' := by
  let e := M.inf (support M (M.inf f.val f'.val)) (support M (M.inf g.val g'.val))
  have he : F.member e := F.filter_inf eqF eqG
  have eq1 := L.agreement_restrict f.property.1 f'.property.1 (F.subunit he) (L.bool.inf_le_left _ _)
  have eq2 := L.agreement_restrict g.property.1 g'.property.1 (F.subunit he) (L.bool.inf_le_right _ _)
  unfold rawRel
  rw [← witness_mem_restrict L F he r f.val g.val, eq1, eq2]
  exact witness_mem_restrict L F he r f'.val g'.val

def relation (r : A) : Points L F → Points L F → Prop :=
  Quotient.lift₂ (rawRel F r) fun _ _ _ _ eqF eqG =>
    propext (rawRel_congr L F r eqF eqG)

theorem relation_point (r : A) (f g : LocalFunction F) :
    relation L F r (point L F f) (point L F g) ↔ rawRel F r f g := Iff.rfl

include L in
private theorem raw_top (f g : LocalFunction F) : rawRel F M.top f g := by
  unfold rawRel
  rw [L.witness_top]
  exact F.filter_inf f.property.2 g.property.2

include L in
private theorem raw_inf (r s : A) (f g : LocalFunction F) :
    rawRel F (M.inf r s) f g ↔ rawRel F r f g ∧ rawRel F s f g := by
  unfold rawRel
  rw [L.witness_inf f.property.1 g.property.1]
  exact mem_inf L (F := F) (L.witness_subunit _ _ _) (L.witness_subunit _ _ _)

include L in
private theorem raw_neg (r : A) (f g : LocalFunction F) :
    rawRel F (M.neg r) f g ↔ ¬rawRel F r f g := by
  have cover : M.sup r (M.neg r) = M.top :=
    L.bool.le_antisymm (L.bool.le_top _ _) (L.bool.le_top r _)
  have hTop := raw_top L F f g
  have either : rawRel F r f g ∨ rawRel F (M.neg r) f g := by
    unfold rawRel at hTop ⊢
    rw [← cover, L.witness_sup] at hTop
    exact (mem_sup L (F := F) (L.witness_subunit _ _ _) (L.witness_subunit _ _ _)).mp hTop
  constructor
  · intro neg positive
    have clash := (raw_inf L F r (M.neg r) f g).mpr ⟨positive, neg⟩
    unfold rawRel at clash
    rw [show M.inf r (M.neg r) = M.zero from L.bool.inf_complement (M.constant .I) r, L.witness_zero] at clash
    exact F.zero_not_mem clash
  · exact either.resolve_left

/-- The quotient of local functions is a square representation for the
literal relation-algebra reduct. Expanded operations need not descend. -/
def square (hM : M.Models preceding) : SquareRepresentation M (Points L F) where
  rel := relation L F
  complement a x y := by
    induction x, y using Quotient.ind₂ with
    | h f g => exact raw_neg L F a f g
  converse a x y := by
    induction x, y using Quotient.ind₂ with
    | h f g =>
      change rawRel F (M.converse a) f g ↔ rawRel F a g f
      unfold rawRel
      rw [L.witness_converse]
  nand a b x y := by
    induction x, y using Quotient.ind₂ with
    | h f g =>
      change rawRel F (M.nand a b) f g ↔ ¬(rawRel F a f g ∧ rawRel F b f g)
      have eq : M.nand a b = M.neg (M.inf a b) := (L.bool.involution _).symm
      rw [eq, raw_neg L F, raw_inf L F]
  universal x y := by
    induction x, y using Quotient.ind₂ with
    | h f g =>
      change rawRel F (M.constant .U) f g ↔ True
      rw [L.universal_top]
      exact ⟨fun _ => trivial, fun _ => raw_top L F f g⟩
  identity x y := by
    induction x, y using Quotient.ind₂ with
    | h f g =>
      change F.member (witness M (M.constant .I) f.val g.val) ↔ point L F f = point L F g
      rw [L.witness_unit]
      change agrees F f g ↔ point L F f = point L F g
      exact ⟨@Quotient.sound _ (functions L F) f g, @Quotient.exact _ (functions L F) f g⟩
  product a b x y := by
    induction x, y using Quotient.ind₂ with
    | h f g =>
      constructor
      · intro edge
        change F.member (witness M (M.product a b) f.val g.val) at edge
        obtain ⟨h, func, supportEq, left, right⟩ := L.witness_intermediate hM a b f.val g.val
        have hMem : F.member (support M h) := by rwa [supportEq]
        let candidate : LocalFunction F := ⟨h, func, hMem⟩
        exact ⟨point L F candidate, F.filter_up hMem left (L.witness_subunit _ _ _),
          F.filter_up hMem right (L.witness_subunit _ _ _)⟩
      · rintro ⟨z, fzh, hzg⟩
        revert fzh hzg
        refine Quotient.inductionOn z ?_
        intro h fzh hzg
        change F.member (witness M (M.product a b) f.val g.val)
        exact F.filter_up (F.filter_inf fzh hzg) (L.witness_compose h.property.1 a b)
          (L.witness_subunit _ _ _)

end PalomarI3380.SubidentityUltrafilter

namespace PalomarI3380.RelationLaws

open Manifest

variable {A : Type} {M : Algebra A} (L : RelationLaws M)
include L

theorem edge_of_filter (hM : M.Models preceding) (F : SubidentityUltrafilter M) {r : A}
    (member : F.member (support M r)) :
    ∃ x y, (SubidentityUltrafilter.square L F hM).rel r x y := by
  have I_mem : F.member (support M (M.constant .I)) := by
    rw [L.support_unit (L.bool.le_refl _)]
    exact F.unit_mem
  let i : SubidentityUltrafilter.LocalFunction F := ⟨M.constant .I, L.identity_functional, I_mem⟩
  let f : SubidentityUltrafilter.LocalFunction F :=
    ⟨M.choice r, L.choice_function hM r, by rwa [L.choice_support hM]⟩
  have chosen : M.le (M.choice r) r := choice_subalgebra hM r
  have diagonal : M.le (support M r) (witness M r (M.constant .I) (M.choice r)) := by
    rw [← L.choice_support hM r, L.support_self, witness, L.unit_left]
    exact L.bool.inf_mono (L.bool.le_refl _) (L.mul_mono_left chosen _)
  exact ⟨SubidentityUltrafilter.point L F i, SubidentityUltrafilter.point L F f,
    F.filter_up member diagonal (L.witness_subunit _ _ _)⟩

/-- A nonzero element of a countable algebra has an edge in a represented square. -/
theorem nonzero_edge (hM : M.Models preceding) (enumerate : Nat → A)
    (surjective : ∀ x, ∃ i, enumerate i = x) {r : A} (nonzero : r ≠ M.zero) :
    ∃ (Point : Type) (S : SquareRepresentation M Point) (x y : Point), S.rel r x y := by
  obtain ⟨F, member⟩ := SubidentityUltrafilter.exists_containing L enumerate surjective
    (support M r) (support_subunit L.bool r) (L.support_nonzero nonzero)
  obtain ⟨a,b,edge⟩ := L.edge_of_filter hM F member
  exact ⟨SubidentityUltrafilter.Points L F,SubidentityUltrafilter.square L F hM,a,b,edge⟩

theorem separates_of_filter (hM : M.Models preceding) (F : SubidentityUltrafilter M)
    (hit : F.member (support M (M.inf (M.constant .D) (M.neg (M.constant .J)))) ∨
      F.member (support M (M.inf (M.constant .J) (M.neg (M.constant .D))))) :
    let S := SubidentityUltrafilter.square L F hM
    ¬∀ x y, S.rel (M.constant .D) x y ↔ S.rel (M.constant .J) x y := by
  let S := SubidentityUltrafilter.square L F hM
  change ¬∀ x y, S.rel (M.constant .D) x y ↔ S.rel (M.constant .J) x y
  intro same
  rcases hit with left | right
  · obtain ⟨x,y,edge⟩ := L.edge_of_filter hM F left
    change S.rel (M.neg (M.nand (M.constant .D) (M.neg (M.constant .J)))) x y at edge
    rw [S.meet,S.complement] at edge
    exact edge.2 ((same x y).mp edge.1)
  · obtain ⟨x,y,edge⟩ := L.edge_of_filter hM F right
    change S.rel (M.neg (M.nand (M.constant .J) (M.neg (M.constant .D)))) x y at edge
    rw [S.meet,S.complement] at edge
    exact edge.2 ((same x y).mpr edge.1)

theorem separating_support (hne : M.constant .D ≠ M.constant .J) :
    support M (M.inf (M.constant .D) (M.neg (M.constant .J))) ≠ M.zero ∨
      support M (M.inf (M.constant .J) (M.neg (M.constant .D))) ≠ M.zero := by
  by_cases empty : M.inf (M.constant .D) (M.neg (M.constant .J)) = M.zero
  · apply Or.inr
    apply L.support_nonzero
    intro other
    apply hne
    exact L.bool.le_antisymm ((L.bool.disjoint_iff_le (M.constant .I) _ _).mp empty)
      ((L.bool.disjoint_iff_le (M.constant .I) _ _).mp other)
  · exact Or.inl (L.support_nonzero empty)

theorem filter_of_distinction (enumerate : Nat → A)
    (surjective : ∀ x, ∃ i, enumerate i = x) (hne : M.constant .D ≠ M.constant .J) :
    ∃ F : SubidentityUltrafilter M,
      F.member (support M (M.inf (M.constant .D) (M.neg (M.constant .J)))) ∨
      F.member (support M (M.inf (M.constant .J) (M.neg (M.constant .D)))) := by
  classical
  let d := M.constant .D
  let j := M.constant .J
  have contains (r : A) (nonzero : r ≠ M.zero) :
      ∃ F : SubidentityUltrafilter M, F.member (support M r) :=
    SubidentityUltrafilter.exists_containing L enumerate surjective
      (support M r) (support_subunit L.bool r) (L.support_nonzero nonzero)
  by_cases h : M.inf d (M.neg j) = M.zero
  · have separated : M.inf j (M.neg d) ≠ M.zero := by
      intro eq
      apply hne
      exact L.bool.le_antisymm ((L.bool.disjoint_iff_le (M.constant .I) _ _).mp h)
        ((L.bool.disjoint_iff_le (M.constant .I) _ _).mp eq)
    obtain ⟨F,member⟩ := contains _ separated
    exact ⟨F,Or.inr member⟩
  · obtain ⟨F,member⟩ := contains _ h
    exact ⟨F,Or.inl member⟩

theorem separated_square (hM : M.Models preceding) (enumerate : Nat → A)
    (surjective : ∀ x, ∃ i, enumerate i = x) (hne : M.constant .D ≠ M.constant .J) :
    ∃ (Point : Type) (S : SquareRepresentation M Point),
      ¬∀ x y, S.rel (M.constant .D) x y ↔ S.rel (M.constant .J) x y := by
  obtain ⟨F,hit⟩ := L.filter_of_distinction enumerate surjective hne
  exact ⟨_,SubidentityUltrafilter.square L F hM,L.separates_of_filter hM F hit⟩

omit L in
theorem separating_term_algebra (h : ¬Derives Manifest.final (.const .D) (.const .J)) :
    ∃ M : Algebra (Derives.Classes Manifest.final),
      M.Models preceding ∧ M.constant .D ≠ M.constant .J := by
  apply Algebra.countermodel_iff.mp
  exact ⟨Derives.termAlgebra Manifest.final,Derives.models_termAlgebra _,
    fun eq => h (Quotient.exact eq)⟩

omit L in
/-- Failure of the target ground equation supplies a genuine separating
square, with the selectors interpreted on the algebra before projection. -/
theorem square_of_underivability (h : ¬ Derives Manifest.final (.const .D) (.const .J)) :
    ∃ (A : Type) (M : Algebra A) (Point : Type) (S : SquareRepresentation M Point),
      M.Models preceding ∧
        ¬ ∀ x y, S.rel (M.constant .D) x y ↔ S.rel (M.constant .J) x y := by
  obtain ⟨M,hM,hne⟩ := separating_term_algebra h
  obtain ⟨enumerate,surjective⟩ := termClasses_countable Manifest.final
  obtain ⟨Point,S,sep⟩ := (of_model M hM).separated_square hM enumerate surjective hne
  exact ⟨_,M,Point,S,hM,sep⟩

end PalomarI3380.RelationLaws
