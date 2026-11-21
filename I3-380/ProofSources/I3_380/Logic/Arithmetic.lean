module
public import I3_380.Logic.SetGraphs
@[expose] public section

namespace PalomarI3380.Logic.SetFormula

/-- Addition follows an internally finite successor recursion. -/
def addition (a b c : Nat) : SetFormula :=
  allOf [natObject a, natObject b, natObject c,
    someSet fun origin => someSet fun domain => someSet fun history =>
      allOf [empty origin, successor b domain, functionOn history domain, graphValue history origin a,
        graphValue history b c,
        eachIn domain fun i => every fun x => implies (graphValue history i x) (natObject x),
        eachIn b fun i => someSet fun j => someSet fun x => someSet fun y =>
          allOf [successor i j, graphValue history i x, graphValue history j y, successor x y]]]

/-- Multiplication follows addition in the same model's natural numbers. -/
def multiplication (a b c : Nat) : SetFormula :=
  allOf [natObject a, natObject b, natObject c,
    someSet fun origin => someSet fun domain => someSet fun history =>
      allOf [empty origin, successor b domain, functionOn history domain, graphValue history origin origin,
        graphValue history b c,
        eachIn domain fun i => every fun x => implies (graphValue history i x) (natObject x),
        eachIn b fun i => someSet fun j => someSet fun x => someSet fun y =>
          allOf [successor i j, graphValue history i x, graphValue history j y, addition x a y]]]

def bitCons (b : Bool) (x y : Nat) : SetFormula :=
  someSet fun bit => someSet fun two => someSet fun twice =>
    allOf [numeral (if b then 1 else 0) bit, numeral 2 two,
      multiplication two x twice, addition bit twice y]

variable {V : Type} {E : V → V → Prop} {d : Nat} {env : Nat → V} {default : V}

set_option maxHeartbeats 3000000 in
theorem holds_addition {a b c : Nat} (ha : a < d) (hb : b < d) (hc : c < d) :
    holds E (addition a b c) d env default ↔ Internal.Add E (env a) (env b) (env c) := by
  simp (disch := omega) only [addition, allOf, holds_both, holds_someSet, holds_empty,
    holds_successor, holds_functionOn, holds_graphValue, holds_eachIn, holds_every, holds_implies,
    holds_natObject, assign_here, assign_earlier, holds_neg, holds_falsity, not_false_eq_true,
    and_true, Internal.Add]
  constructor
  · rintro ⟨na, nb, nc, z, domain, f, empty, succ, function, initial, final, values, steps⟩
    exact ⟨na, nb, nc, z, domain, f, empty, succ, function, initial, final,
      fun i x id => values i id x, steps⟩
  · rintro ⟨na, nb, nc, z, domain, f, empty, succ, function, initial, final, values, steps⟩
    exact ⟨na, nb, nc, z, domain, f, empty, succ, function, initial, final,
      fun i id x => values i x id, steps⟩

set_option maxHeartbeats 3000000 in
theorem holds_multiplication {a b c : Nat} (ha : a < d) (hb : b < d) (hc : c < d) :
    holds E (multiplication a b c) d env default ↔ Internal.Mul E (env a) (env b) (env c) := by
  simp (disch := omega) only [multiplication, allOf, holds_both, holds_someSet, holds_empty,
    holds_successor, holds_functionOn, holds_graphValue, holds_eachIn, holds_every, holds_implies,
    holds_natObject, assign_here, assign_earlier, holds_neg, holds_falsity, not_false_eq_true,
    and_true, holds_addition, Internal.Mul]
  constructor
  · rintro ⟨na, nb, nc, z, domain, f, empty, succ, function, initial, final, values, steps⟩
    exact ⟨na, nb, nc, z, domain, f, empty, succ, function, initial, final,
      fun i x id => values i id x, steps⟩
  · rintro ⟨na, nb, nc, z, domain, f, empty, succ, function, initial, final, values, steps⟩
    exact ⟨na, nb, nc, z, domain, f, empty, succ, function, initial, final,
      fun i id x => values i x id, steps⟩

theorem holds_bitCons (b : Bool) {x y : Nat} (hx : x < d) (hy : y < d) :
    holds E (bitCons b x y) d env default ↔ Internal.BitCons E b (env x) (env y) := by
  simp (disch := omega) only [bitCons, allOf, holds_someSet, holds_both, holds_numeral,
    holds_multiplication, holds_addition, assign_here, assign_earlier, holds_neg,
    holds_falsity, not_false_eq_true, and_true, Internal.BitCons]

end PalomarI3380.Logic.SetFormula
