module
public import I3_334.Proof.DisjointElementarity
public import I3_334.Proof.SafeTerms
public import I3_334Support.SetTheory.Classes.ModelLocalEvaluation
@[expose] public section

namespace PalomarI3334

open PalomarI3380 PalomarI3380.Logic
open SquareRepresentation (SetContext)

namespace RankPreservation

variable {V : Type} (D : V → Prop)

abbrev In := {x : V // D x}
abbrev Out := {x : V // ¬D x}

def joinPoint : Sum (In D) (Out D) → V
  | .inl x => x.val
  | .inr x => x.val

noncomputable def splitPoint (x : V) : Sum (In D) (Out D) := by
  classical
  exact if h : D x then .inl ⟨x, h⟩ else .inr ⟨x, h⟩

theorem join_split (x : V) : joinPoint D (splitPoint D x) = x := by
  classical
  unfold splitPoint
  split <;> rfl

theorem split_join (x : Sum (In D) (Out D)) : splitPoint D (joinPoint D x) = x := by
  classical
  cases x with
  | inl x => simp [joinPoint, splitPoint, x.property]
  | inr x => simp [joinPoint, splitPoint, x.property]

theorem join_injective : Function.Injective (joinPoint D) :=
  fun _ _ eq => by simpa only [split_join] using congrArg (splitPoint D) eq

variable (E : V → V → Prop)

theorem join_relation (closed : ∀ x y, E x y → D y → D x) (x y : Sum (In D) (Out D)) :
    Disjoint.relation (fun x y : In D => E x.val y.val) (fun _ _ => False) x y ↔
      E (joinPoint D x) (joinPoint D y) ∧ D (joinPoint D y) := by
  cases x with
  | inl x =>
    cases y with
    | inl y => simp [joinPoint, Disjoint.relation, y.property]
    | inr y => simp [joinPoint, Disjoint.relation, y.property]
  | inr x =>
    cases y with
    | inl y => exact ⟨False.elim, fun ⟨edge, inside⟩ => x.property (closed _ _ edge inside)⟩
    | inr y => simp [joinPoint, Disjoint.relation, y.property]

theorem preserves (closed : ∀ x y, E x y → D y → D x)
    (j : In D → In D) (inside : In D) (outside : Out D)
    (elem : ∀ p env, LocalFormula.eval (fun x y : In D => E x.val y.val) (fun _ => True) p env ↔
      LocalFormula.eval (fun x y : In D => E x.val y.val) (fun _ => True) p (j ∘ env))
    (t : SafeTerm) (x y : In D) :
    t.rel (fun a b => E a b ∧ D b) x.val y.val ↔
      t.rel (fun a b => E a b ∧ D b) (j x).val (j y).val := by
  let env : Fin 3 → Sum (In D) (Out D) := fun i => if i = 1 then .inl y else .inl x
  let R := fun a b : In D => E a.val b.val
  let S := fun _ _ : Out D => False
  let K := fun a b => E a b ∧ D b
  let outer := joinPoint D
  let p := t.formula 0 1
  have same (values : Fin 3 → Sum (In D) (Out D)) :
      LocalFormula.eval (Disjoint.relation R S) (fun _ => True) p values ↔
        LocalFormula.eval K (fun _ => True) p (outer ∘ values) := by
    have relation : Disjoint.relation R S = fun x y => K (outer x) (outer y) :=
      funext fun x => funext fun y => propext (join_relation D E closed x y)
    rw [relation]
    exact Logic.eval_along outer (join_injective D) K (fun _ => True)
      (fun x => ⟨fun _ => ⟨splitPoint D x, join_split D x⟩, fun _ => trivial⟩) p values
  have invariant := Disjoint.elementary R S j inside outside elem p env
  have transported := (same env).symm.trans (invariant.trans (same _))
  exact ((SafeTerm.formula_eval K t (outer ∘ env) 0 1).symm.trans
      (transported.trans (SafeTerm.formula_eval K t (outer ∘ Sum.map j id ∘ env) 0 1)))

end RankPreservation

end PalomarI3334
