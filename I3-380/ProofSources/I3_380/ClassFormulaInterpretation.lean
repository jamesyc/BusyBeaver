module
public import I3_380.ForcingTruth
@[expose] public section

namespace PalomarI3380.Logic.Expanded.ClassRelation

open SquareRepresentation

variable {V : Type} {E G : V → V → Prop}

private theorem atom_formula (r : ClassRelation E G) (a b : Argument V) {n : Nat}
    (ha : a.bound n) (hb : b.bound n) :
    ∃ p : RelationFormula (ClassRelation E G), p.Bound n ∧
      ∀ s, RelationFormula.eval (square E G) p s ↔ r.holds (a.value s) (b.value s) := by
  cases a with
  | «variable» i =>
    cases b with
    | «variable» j => exact ⟨.atom r i j,⟨ha,hb⟩,fun _ => Iff.rfl⟩
    | named v =>
      let unary : ClassRelation E G := ⟨fun x _ => r.holds x v,⟨r.reference (.variable 0) (.named v),
        r.reference_bound (Nat.zero_lt_succ 1) trivial, r.reference_eval _ _⟩⟩
      exact ⟨.atom unary i i,⟨ha,ha⟩,fun _ => Iff.rfl⟩
  | named u =>
    cases b with
    | «variable» j =>
      let unary : ClassRelation E G := ⟨fun x _ => r.holds u x,⟨r.reference (.named u) (.variable 0),
        r.reference_bound trivial (Nat.zero_lt_succ 1), r.reference_eval _ _⟩⟩
      exact ⟨.atom unary j j,⟨hb,hb⟩,fun _ => Iff.rfl⟩
    | named v =>
      classical
      by_cases h : r.holds u v
      · exact ⟨.imp .bot .bot,⟨trivial,trivial⟩,fun _ => ⟨fun _ => h,fun _ => id⟩⟩
      · exact ⟨.bot,trivial,fun _ => ⟨False.elim,h⟩⟩

/-- Interpret an expanded formula in the algebra of its definable
relations. Names can be put into unary relations without a new free
variable. -/
theorem interpret_formula (p : Formula V) {n : Nat} (scope : Bound p n) :
    (square E G).Definable n (fun s => eval E G p s) := by
  induction p generalizing n with
  | bot => exact ⟨.bot,trivial,fun _ => Iff.rfl⟩
  | eq a b => exact atom_formula one a b scope.1 scope.2
  | mem a b => exact atom_formula member a b scope.1 scope.2
  | order a b => exact atom_formula ⟨G,Binary.globalOrder⟩ a b scope.1 scope.2
  | and a b ia ib => exact (ia scope.1).and (ib scope.2)
  | or a b ia ib => exact (ia scope.1).or (ib scope.2)
  | imp a b ia ib => exact (ia scope.1).implies (ib scope.2)
  | all a ih => exact Definable.all (ih scope)
  | ex a ih => exact Definable.ex (ih scope)

end PalomarI3380.Logic.Expanded.ClassRelation

namespace PalomarI3380.SquareRepresentation.SetContext.OrdinaryContext

open Logic
variable {V : Type} {E : V → V → Prop} (h : ZFCModel E) (inhabited : Nonempty V)

theorem base_definition {n : Nat} (f : Expanded.Formula V) (scope : Expanded.Bound f n) :
    (underlying h inhabited).square.Definable n
      (fun s => Expanded.eval E (fun _ _ => False) f s) :=
  Expanded.ClassRelation.interpret_formula f scope

end PalomarI3380.SquareRepresentation.SetContext.OrdinaryContext
