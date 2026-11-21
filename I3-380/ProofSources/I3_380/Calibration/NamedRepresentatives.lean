module
public import I3_380.Calibration.PointInterpretation
public import I3_380.RelationAlgebra.Representation
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder Manifest RelationLaws SquareRepresentation
open SubidentityUltrafilter (LocalFunction Points point agrees rawRel)

variable {A : Type} [Tarski.Structure FilterLanguage A] [Tarski.Structure.Eq FilterLanguage A]

local notation "M" => algebraOf A

structure FilterModel (A : Type) [Tarski.Structure FilterLanguage A] where
  laws : (algebraOf A).Models preceding
  filter : SubidentityUltrafilter (algebraOf A)
  predicate : filter.member = chosenOf A

namespace FilterModel

variable (C : FilterModel A)

def relationLaws : RelationLaws (M) := RelationLaws.of_model _ C.laws

abbrev square := SubidentityUltrafilter.square C.relationLaws C.filter C.laws

abbrev Domain := {p : Points C.relationLaws C.filter // C.square.Named p}

abbrev Representative := {r : LocalFunction C.filter // C.square.Named (point C.relationLaws C.filter r)}

def asPoint (f : C.Representative) : C.Domain := ⟨point C.relationLaws C.filter f.val,f.property⟩

theorem asPoint_onto (p : C.Domain) : ∃ f, C.asPoint f = p := by
  obtain ⟨f,eq⟩ := Quotient.exists_rep p.val
  have exactPoint : point C.relationLaws C.filter f = p.val := eq
  have named : C.square.Named (point C.relationLaws C.filter f) := by
    rw [exactPoint]
    exact p.property
  exact ⟨⟨f,named⟩,Subtype.ext exactPoint⟩

def mem (p q : C.Domain) : Prop := C.square.rel ((M).constant .E) p.val q.val

theorem matches_membership (p q : C.Representative) :
    membershipOp.sentence.Evalb ![p.val.val,q.val.val] ↔ C.mem (C.asPoint p) (C.asPoint q) := by
  refine (membershipOp_eval (A := A) p.val.val q.val.val).trans ?_
  change chosenOf A (witness (M) ((M).constant .E) p.val.val q.val.val) ↔
    C.filter.member (witness (M) ((M).constant .E) p.val.val q.val.val)
  exact Iff.of_eq (congrFun C.predicate _).symm

theorem point_eq_iff (x y : LocalFunction C.filter) :
    C.filter.member (support (M) ((M).inf x.val y.val)) ↔
      point C.relationLaws C.filter x = point C.relationLaws C.filter y :=
  ⟨fun h => Quotient.sound (show agrees C.filter x y from h),fun h => Quotient.exact h⟩

theorem matches_equality (p q : C.Representative) :
    agreementOp.sentence.Evalb ![p.val.val,q.val.val] ↔ C.asPoint p = C.asPoint q := by
  refine (agreementOp_eval ..).trans ?_
  rw [← C.predicate]
  exact ⟨fun h => Subtype.ext (Quotient.sound (show agrees C.filter p.val q.val from h)),
    fun h => Quotient.exact (congrArg Subtype.val h)⟩

theorem representative_eval (a : A) :
    namedPointOp.sentence.Evalb ![a] ↔ ∃ f : C.Representative, f.val.val = a := by
  rw [namedPointOp_eval,← C.predicate]
  constructor
  · rintro ⟨sub,⟨d,rule⟩⟩
    let f : LocalFunction C.filter := ⟨a,sub⟩
    have named : C.square.Named (point C.relationLaws C.filter f) := by
      refine ⟨d,fun x y => ?_⟩
      induction x, y using Quotient.ind₂ with
      | h x y =>
        refine (rule x.val y.val ⟨x.property,y.property⟩).trans ?_
        exact and_congr (C.point_eq_iff x f) (C.point_eq_iff y f)
    exact ⟨⟨f,named⟩,rfl⟩
  · rintro ⟨f,rfl⟩
    obtain ⟨d,rule⟩ := f.property
    refine ⟨f.val.property,d,fun x y ⟨hx,hy⟩ => ?_⟩
    have uses := rule (point C.relationLaws C.filter ⟨x,hx⟩)
      (point C.relationLaws C.filter ⟨y,hy⟩)
    exact uses.trans (and_congr (C.point_eq_iff ⟨x,hx⟩ f.val).symm
      (C.point_eq_iff ⟨y,hy⟩ f.val).symm)

end FilterModel
end PalomarI3380.Calibration
