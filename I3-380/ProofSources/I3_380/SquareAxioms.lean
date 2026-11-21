module
public import I3_380.SquareSchemas
public import I3_380.RelationAlgebra.Representation
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic Manifest

/-- The fixed membership axioms obtained directly from pictures of
relations. The two remaining fixed axioms need the stage argument. -/
def BaseAxiom (p : Formula) : Prop :=
  p = fixedRefl ∨ p = fixedSym ∨ p = fixedTrans ∨ p = fixedEqElem ∨
  p = fixedExt ∨ p = fixedEmpty ∨ p = fixedPair ∨ p = fixedUnion ∨
  p = fixedPower ∨ p = choiceAxiom

variable {A Point : Type} {M : Algebra A} {S : SquareRepresentation M Point}

theorem satisfies_choice (P : QuasiProjections S) (hM : M.Models preceding)
    (names : ∀ x, S.Named x)
    (pairs : ∀ a b, ∃ p, Internal.Pair (S.rel (M.constant .E)) a b p) (env : Nat → Point) :
    eval (S.rel (M.constant .E)) choiceAxiom env := by
  let E := S.rel (M.constant .E)
  let choice := SetFormula.every fun family =>
    SetFormula.implies (SetFormula.eachIn family fun x =>
      SetFormula.someIn x fun y => SetFormula.eq y y)
      (SetFormula.someSet fun f => SetFormula.both (SetFormula.functionOn f family)
        (SetFormula.eachIn family fun x => SetFormula.every fun y =>
          SetFormula.implies (SetFormula.graphValue f x y) (SetFormula.mem y x)))
  have meaning : SetFormula.holds E choice 0 env (env 0) := by
    simp (disch := omega) only [choice, SetFormula.holds_every, SetFormula.holds_implies,
      SetFormula.holds_eachIn, SetFormula.holds_someIn, SetFormula.holds_eq, SetFormula.holds_someSet,
      SetFormula.holds_both, SetFormula.holds_functionOn, SetFormula.holds_graphValue,
      SetFormula.holds_mem, SetFormula.assign_here, SetFormula.assign_earlier, and_true]
    intro family members
    obtain ⟨f, hf, chooses⟩ := choice_function P hM names pairs family members
    exact ⟨f, hf, fun x hx y hxy => chooses x y hx hxy⟩
  exact (eval_congr_bound choiceAxiom choice_closed (fun i hi => by omega)).mp
    (show eval E choiceAxiom (SetFormula.assignment 0 env (env 0)) from meaning)

theorem base_axioms (P : QuasiProjections S) (hM : M.Models preceding)
    (names : ∀ x, S.Named x)
    (pairs : ∀ a b, ∃ p, Internal.Pair (S.rel (M.constant .E)) a b p)
    (p : Formula) (isAxiom : BaseAxiom p) (env : Nat → Point) :
    eval (S.rel (M.constant .E)) p env := by
  rcases isAxiom with h | h | h | h | h | h | h | h | h | h <;> subst p
  · exact fun _ => rfl
  · exact fun _ _ => Eq.symm
  · exact fun _ _ _ => Eq.trans
  · simp only [fixedEqElem, eval, pushValue]
    intro a b c d h₁ h₂ h
    simpa only [← h₁, ← h₂] using h
  · intro x y xy yx
    exact S.extensional hM fun z => ⟨xy z, yx z⟩
  · exact S.exists_empty hM (env 0)
  · intro x y
    obtain ⟨p, hp⟩ := pairs x y
    exact ⟨p, fun z => ⟨(hp z).mp, (hp z).mpr⟩⟩
  · intro x
    obtain ⟨u, hu⟩ := S.union_set hM names pairs x
    exact ⟨u, fun z => ⟨(hu z).mp, (hu z).mpr⟩⟩
  · intro x
    obtain ⟨q, hq⟩ := S.powerset hM names pairs x
    exact ⟨q, fun z => ⟨(hq z).mp, (hq z).mpr⟩⟩
  · exact satisfies_choice P hM names pairs env

/-- Set operations with Separation and Replacement for the chosen
first-order language. The structure is independent of the machine's
stage and embedding equations. -/
structure SetContext (M : Algebra A) (Point : Type) where
  square : SquareRepresentation M Point
  inhabited : Nonempty Point
  extensional : Internal.Extensional (square.rel (M.constant .E))
  emptySet : ∃ p, Internal.Empty (square.rel (M.constant .E)) p
  pairs : ∀ a b, ∃ p, Internal.Pair (square.rel (M.constant .E)) a b p
  powerSet : ∀ a, ∃ p, ∀ x, square.rel (M.constant .E) x p ↔
    ∀ z, square.rel (M.constant .E) z x → square.rel (M.constant .E) z a
  unionSet : ∀ a, ∃ u, ∀ x, square.rel (M.constant .E) x u ↔
    ∃ y, square.rel (M.constant .E) y a ∧ square.rel (M.constant .E) x y
  subsetRel : ∀ a b, square.rel (M.constant .T) a b ↔
    ∀ x, square.rel (M.constant .E) x a → square.rel (M.constant .E) x b
  choiceSet : ∀ family, (∀ x, square.rel (M.constant .E) x family → ∃ y, square.rel (M.constant .E) y x) →
    ∃ f, Internal.FunctionOn (square.rel (M.constant .E)) f family ∧
      ∀ x y, square.rel (M.constant .E) x family →
        Internal.At (square.rel (M.constant .E)) f x y → square.rel (M.constant .E) y x
  separates : ∀ (params : List Point) (formula : RelationFormula A),
    formula.Bound (params.length + 2) → ∀ input anchor,
    ∃ output, ∀ x, square.rel (M.constant .E) x output ↔
      square.rel (M.constant .E) x input ∧ RelationFormula.eval square formula (parameterEnv params x anchor)
  replaces : ∀ (params : List Point) (formula : RelationFormula A),
    formula.Bound (params.length + 2) →
    (∀ x y z, RelationFormula.eval square formula (parameterEnv params x y) →
      RelationFormula.eval square formula (parameterEnv params x z) → y = z) →
    ∀ input, ∃ output, ∀ y, square.rel (M.constant .E) y output ↔
      ∃ x, square.rel (M.constant .E) x input ∧ RelationFormula.eval square formula (parameterEnv params x y)

structure NamedModel (M : Algebra A) (Point : Type) extends SetContext M Point where
  laws : M.Models preceding
  names : ∀ x, square.Named x
  projections : QuasiProjections square
  movement : ∃ x y, square.rel (M.constant .J) x y ∧ x ≠ y

instance : Coe (NamedModel M Point) (SetContext M Point) := ⟨NamedModel.toSetContext⟩

theorem namedModel_of_separated {M : Algebra A} {Point : Type}
    (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (sep : ¬∀ x y, S.rel (M.constant .D) x y ↔ S.rel (M.constant .J) x y) :
    ∃ N : NamedModel M {p : Point // S.Named p}, N.square = S.namedSquare hM := by
  obtain ⟨x, y, hx, hy, move, ne⟩ := S.named_moved hM sep
  obtain ⟨projections⟩ := S.named_hull_projections hM sep
  let square := S.namedSquare hM
  have names := S.every_named hM
  have pairs := S.named_hull_pairs hM sep
  let context : SetContext M {x : Point // S.Named x} := {
    square := square
    inhabited := ⟨⟨x, hx⟩⟩
    extensional := square.internal_extensional hM
    emptySet := square.exists_empty hM ⟨x, hx⟩
    pairs := pairs
    powerSet := square.powerset hM names pairs
    unionSet := square.union_set hM names pairs
    subsetRel := square.subset_iff hM
    choiceSet := choice_function projections hM names pairs
    separates := square.separation projections hM names
    replaces := definable_image projections hM names
  }
  exact ⟨⟨context, hM, names, projections, ⟨⟨x, hx⟩, ⟨y, hy⟩, move,
    fun same => ne (congrArg Subtype.val same)⟩⟩,rfl⟩

theorem namedModel_of_underivability (h : ¬ Derives final (.const .D) (.const .J)) :
    ∃ (A : Type) (M : Algebra A) (Point : Type), Nonempty (NamedModel M Point) := by
  obtain ⟨A,M,Point,S,hM,sep⟩ := RelationLaws.square_of_underivability h
  obtain ⟨N,_⟩ := S.namedModel_of_separated hM sep
  exact ⟨A,M,_,⟨N⟩⟩

end PalomarI3380.SquareRepresentation
