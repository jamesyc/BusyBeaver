module
public import I3_334Support.SetTheory.Square.SquareSets
public import I3_334Support.Logic.SetPairs
public import I3_334Support.Logic.SetScope
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic Manifest

variable {A Point : Type} {M : Algebra A} {S : SquareRepresentation M Point}

theorem internal_extensional (S : SquareRepresentation M Point) (hM : M.Models preceding) :
    Internal.Extensional (S.rel (M.constant .E)) := by
  intro a b same
  exact S.extensional hM same

/-- The graph of the selected element of each member of a family exists
by exact image. The graph is a set of actual Kuratowski codes. -/
theorem choice_function (P : QuasiProjections S) (hM : M.Models preceding)
    (names : ∀ x, S.Named x)
    (pairs : ∀ a b, ∃ p, Internal.Pair (S.rel (M.constant .E)) a b p) (family : Point)
    (nonempty : ∀ x, S.rel (M.constant .E) x family → ∃ y, S.rel (M.constant .E) y x) :
    ∃ f, Internal.FunctionOn (S.rel (M.constant .E)) f family ∧
      ∀ x y, S.rel (M.constant .E) x family →
        Internal.At (S.rel (M.constant .E)) f x y → S.rel (M.constant .E) y x := by
  let e := M.constant .E
  let select := M.choice (M.converse e)
  let pairFormula := SetFormula.orderedPair 1 2 0 3
  let formula : RelationFormula A :=
    .ex (.and (.atom select 1 0) (RelationFormula.liftMembership e pairFormula))
  have pairBound : Bound pairFormula 3 :=
    SetFormula.scope_orderedPair (a := 1) (b := 2) (p := 0) (by decide) (by decide) (by decide)
  have formulaBound : formula.Bound (2 : Nat) := by
    change (1 < 3 ∧ 0 < 3) ∧ (RelationFormula.liftMembership e pairFormula).Bound 3
    exact ⟨by decide, (RelationFormula.liftMembership_bound e pairFormula 3).mpr pairBound⟩
  have input (x code : Point) :
      RelationFormula.eval S formula (parameterEnv [] x code) ↔
        ∃ y, S.rel select x y ∧ Internal.OrderedPair (S.rel e) x y code := by
    change (∃ y, S.rel select x y ∧ RelationFormula.eval S
      (RelationFormula.liftMembership e pairFormula) (pushValue (parameterEnv [] x code) y)) ↔ _
    apply exists_congr
    intro y
    apply and_congr_right
    intro _
    rw [RelationFormula.liftMembership_eval]
    refine (SetFormula.eval_levels (d := 3) (default := x) (SetFormula.orderedPair 1 2 0) pairBound).trans ?_
    exact SetFormula.holds_orderedPair (E := S.rel e) (a := 1) (b := 2) (p := 0) (d := 3)
      (env := fun i => pushValue (parameterEnv [] x code) y (3 - (i + 1)))
      (default := x) (by decide) (by decide) (by decide)
  have functionality (x p q : Point) (hp : RelationFormula.eval S formula (parameterEnv [] x p))
      (hq : RelationFormula.eval S formula (parameterEnv [] x q)) : p = q := by
    obtain ⟨y, hy, hpair⟩ := (input x p).mp hp
    obtain ⟨z, hz, hpair'⟩ := (input x q).mp hq
    cases S.choice_functional hM (M.converse e) hy hz
    exact Internal.orderedPair_unique (S.internal_extensional hM) hpair hpair'
  obtain ⟨f, hf⟩ := definable_image P hM names [] formula formulaBound functionality family
  have graph (code : Point) : S.rel e code f ↔ ∃ x y, S.rel e x family ∧
      S.rel select x y ∧ Internal.OrderedPair (S.rel e) x y code := by
    refine (hf code).trans ?_
    constructor
    · rintro ⟨x, hx, h⟩
      obtain ⟨y, hy, hp⟩ := (input x code).mp h
      exact ⟨x, y, hx, hy, hp⟩
    · rintro ⟨x, y, hx, hy, hp⟩
      exact ⟨x, hx, (input x code).mpr ⟨y, hy, hp⟩⟩
  have value (x y : Point) : Internal.At (S.rel e) f x y ↔ S.rel e x family ∧ S.rel select x y := by
    constructor
    · rintro ⟨p, hp, code⟩
      obtain ⟨x', y', hx', hy', code'⟩ := (graph p).mp hp
      obtain ⟨rfl, rfl⟩ := Internal.orderedPair_injective code code'
      exact ⟨hx', hy'⟩
    · rintro ⟨hx, hy⟩
      obtain ⟨p, hp⟩ := Internal.orderedPair_exists pairs x y
      exact ⟨p, (graph p).mpr ⟨x, y, hx, hy, hp⟩, hp⟩
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, hy⟩ := nonempty x hx
    obtain ⟨z, hz⟩ := (S.choice_domain hM (M.converse e) x).mpr
      ⟨y, (S.converse _ _ _).mpr hy⟩
    exact ⟨z, (value x z).mpr ⟨hx, hz⟩, fun w hw =>
      S.choice_functional hM (M.converse e) ((value x w).mp hw).2 hz⟩
  · intro p hp
    obtain ⟨x, y, hx, _, code⟩ := (graph p).mp hp
    exact ⟨x, y, hx, code⟩
  · intro x y _ hxy
    exact (S.converse _ _ _).mp (S.choice_sub hM _ ((value x y).mp hxy).2)

end PalomarI3380.SquareRepresentation
