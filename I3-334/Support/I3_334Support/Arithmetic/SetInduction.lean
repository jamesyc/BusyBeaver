module
public import I3_334Support.Arithmetic.SetArithmetic
public import I3_334Support.SetTheory.Recursion.OmegaSets
@[expose] public section

namespace PalomarI3380.Logic.Expanded

open SquareRepresentation

variable {V : Type} {E G : V → V → Prop} {laws : ClassAxioms E G} {inhabited : Nonempty V}
variable (D : OmegaDomain laws inhabited)

/-- Induction on the model's natural numbers for a set formula whose
parameters can include the truth table or other objects outside omega. -/
theorem OmegaDomain.setOrderInduction (params : List V) (anchor : V)
    (P : D.Points → Prop) {pred : (Nat → V) → Prop}
    (described : (laws.context inhabited).square.Definable (params.length+2) pred)
    (meaning : ∀ a : D.Points, pred (parameterEnv params a.val anchor) ↔ P a)
    (step : ∀ a, (∀ b, E b.val a.val → P b) → P a) :
    ∀ a, P a := by
  classical
  let N := laws.context inhabited
  have ordinal := N.omega_ordinal D.specification
  obtain ⟨bad,membership⟩ := N.separate params described.not D.omega anchor
  have badSpec (a : D.Points) : N.mem a.val bad ↔ ¬P a := by
    rw [membership a.val]
    change (E a.val D.omega ∧ ¬pred (parameterEnv params a.val anchor)) ↔ _
    rw [meaning a]
    exact ⟨And.right,fun h => ⟨a.property,h⟩⟩
  intro a
  by_contra no
  have subset : N.Subset bad D.omega := fun x hx => ((membership x).mp hx).1
  obtain ⟨least,inBad,minimal⟩ := ordinal.exists_least N subset ⟨a.val,(badSpec a).mpr no⟩
  let point : D.Points := ⟨least,subset _ inBad⟩
  apply (badSpec point).mp inBad
  apply step point
  intro b before
  by_contra h
  have bBad := (badSpec b).mpr h
  rcases minimal b.val bBad with eq | after
  · subst least
    exact ordinal.ordered.irrefl b.val b.property before
  · exact ordinal.ordered.asymm N point.property b.property after before

end PalomarI3380.Logic.Expanded
