module
public import I3_334Support.Logic.SetSemantics
public import I3_334Support.Logic.History
@[expose] public section

namespace PalomarI3380.Logic.SetFormula

variable {V : Type} {E : V → V → Prop} {d : Nat} {env : Nat → V} {default : V}

theorem holds_empty {a : Nat} (ha : a < d) :
    holds E (empty a) d env default ↔ Internal.Empty E (env a) := by
  simp (disch := omega) only [empty, holds_every, holds_neg, holds_mem, assign_here, assign_earlier,
    Internal.Empty]

theorem holds_subset {a b : Nat} (ha : a < d) (hb : b < d) :
    holds E (subset a b) d env default ↔ (∀ x, E x (env a) → E x (env b)) := by
  simp (disch := omega) only [subset, holds_eachIn, holds_mem, assign_here, assign_earlier]

theorem holds_successor {a b : Nat} (ha : a < d) (hb : b < d) :
    holds E (successor a b) d env default ↔ Internal.Succ E (env a) (env b) := by
  simp (disch := omega) only [successor, holds_every, holds_iff, holds_either, holds_mem, holds_eq,
    assign_here, assign_earlier, Internal.Succ]

theorem holds_numeral (n : Nat) {a : Nat} (ha : a < d) :
    holds E (numeral n a) d env default ↔ Internal.Numeral E n (env a) := by
  induction n generalizing d env a with
  | zero => exact holds_empty ha
  | succ n ih =>
    simp (disch := omega) only [numeral, holds_someSet, holds_both, holds_successor, ih,
      assign_here, assign_earlier, Internal.Numeral]

theorem holds_unorderedPair {a b p : Nat} (ha : a < d) (hb : b < d) (hp : p < d) :
    holds E (unorderedPair a b p) d env default ↔ Internal.Pair E (env a) (env b) (env p) := by
  simp (disch := omega) only [unorderedPair, holds_every, holds_iff, holds_either, holds_mem, holds_eq,
    assign_here, assign_earlier, Internal.Pair]

theorem holds_orderedPair {a b p : Nat} (ha : a < d) (hb : b < d) (hp : p < d) :
    holds E (orderedPair a b p) d env default ↔ Internal.OrderedPair E (env a) (env b) (env p) := by
  simp (disch := omega) only [orderedPair, holds_someSet, allOf, holds_both, holds_neg,
    holds_falsity, not_false_eq_true, and_true, holds_unorderedPair, assign_here, assign_earlier,
    Internal.OrderedPair]

theorem holds_graphValue {f x y : Nat} (hf : f < d) (hx : x < d) (hy : y < d) :
    holds E (graphValue f x y) d env default ↔ Internal.At E (env f) (env x) (env y) := by
  simp (disch := omega) only [graphValue, holds_someIn, holds_orderedPair, assign_here, assign_earlier,
    Internal.At]

theorem holds_functionOn {f domain : Nat} (hf : f < d) (hd : domain < d) :
    holds E (functionOn f domain) d env default ↔ Internal.FunctionOn E (env f) (env domain) := by
  simp (disch := omega) only [functionOn, holds_both, holds_eachIn, holds_someIn, holds_someSet,
    holds_orderedPair, holds_graphValue, holds_every, holds_implies, holds_eq, assign_here, assign_earlier,
    Internal.FunctionOn]
  constructor
  · rintro ⟨domainSpec, values⟩
    refine ⟨values, fun p hp => ?_⟩
    obtain ⟨x, hx, y, pair⟩ := domainSpec p hp
    exact ⟨x, y, hx, pair⟩
  · rintro ⟨values, domainSpec⟩
    refine ⟨fun p hp => ?_, values⟩
    obtain ⟨x, y, hx, pair⟩ := domainSpec p hp
    exact ⟨x, hx, y, pair⟩

theorem holds_inductiveSet {a : Nat} (ha : a < d) :
    holds E (inductiveSet a) d env default ↔ Internal.Inductive E (env a) := by
  simp (disch := omega) only [inductiveSet, holds_both, holds_someIn, holds_eachIn, holds_empty,
    holds_successor, assign_here, assign_earlier, Internal.Inductive]
  exact and_congr (exists_congr fun x => and_comm) (forall_congr' fun _ => imp_congr Iff.rfl
    (exists_congr fun _ => and_comm))

theorem holds_omegaSet {a : Nat} (ha : a < d) :
    holds E (omegaSet a) d env default ↔ Internal.Omega E (env a) := by
  simp (disch := omega) only [omegaSet, holds_both, holds_every, holds_implies,
    holds_inductiveSet, holds_subset, assign_here, assign_earlier, Internal.Omega]

def natObject (a : Nat) : SetFormula :=
  someSet fun w => both (omegaSet w) (mem a w)

theorem holds_natObject {a : Nat} (ha : a < d) :
    holds E (natObject a) d env default ↔ Internal.NatObject E (env a) := by
  simp (disch := omega) only [natObject, holds_someSet, holds_both, holds_omegaSet, holds_mem,
    assign_here, assign_earlier, Internal.NatObject]

end PalomarI3380.Logic.SetFormula
