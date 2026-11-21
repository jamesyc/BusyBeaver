module
public import I3_380.Logic.Arithmetic
@[expose] public section

namespace PalomarI3380.Logic.SetFormula

def Scoped (depth : Nat) (p : SetFormula) : Prop := Bound (p depth) depth

theorem scope_falsity (d : Nat) : Scoped d falsity := trivial
theorem scope_eq {d x y : Nat} (hx : x < d) (hy : y < d) : Scoped d (eq x y) := by
  change d - (x + 1) < d ∧ d - (y + 1) < d
  omega
theorem scope_mem {d x y : Nat} (hx : x < d) (hy : y < d) : Scoped d (mem x y) := by
  change d - (x + 1) < d ∧ d - (y + 1) < d
  omega

theorem scope_both (d : Nat) (p q : SetFormula) :
    Scoped d (both p q) ↔ Scoped d p ∧ Scoped d q := Iff.rfl
theorem scope_either (d : Nat) (p q : SetFormula) :
    Scoped d (either p q) ↔ Scoped d p ∧ Scoped d q := Iff.rfl
theorem scope_impl (d : Nat) (p q : SetFormula) :
    Scoped d (implies p q) ↔ Scoped d p ∧ Scoped d q := Iff.rfl
theorem scope_neg (d : Nat) (p : SetFormula) : Scoped d (neg p) ↔ Scoped d p :=
  ⟨And.left, fun hp => ⟨hp, trivial⟩⟩
theorem scope_iff (d : Nat) (p q : SetFormula) :
    Scoped d (iff p q) ↔ Scoped d p ∧ Scoped d q :=
  ⟨fun h => h.1, fun h => ⟨h, h.symm⟩⟩

theorem scope_every (d : Nat) (p : Nat → SetFormula) :
    Scoped d (every p) ↔ Scoped (d + 1) (p d) := Iff.rfl
theorem scope_someSet (d : Nat) (p : Nat → SetFormula) :
    Scoped d (someSet p) ↔ Scoped (d + 1) (p d) := Iff.rfl

theorem scope_eachIn {d a : Nat} (ha : a < d) (p : Nat → SetFormula) :
    Scoped d (eachIn a p) ↔ Scoped (d + 1) (p d) := by
  simp (disch := omega) only [eachIn, scope_every, scope_impl, scope_mem, true_and]

theorem scope_someIn {d a : Nat} (ha : a < d) (p : Nat → SetFormula) :
    Scoped d (someIn a p) ↔ Scoped (d + 1) (p d) := by
  simp (disch := omega) only [someIn, scope_someSet, scope_both, scope_mem, true_and]

theorem scope_allOf (d : Nat) (ps : List SetFormula) :
    Scoped d (allOf ps) ↔ ∀ p ∈ ps, Scoped d p := by
  induction ps with
  | nil => simp [allOf, scope_neg, scope_falsity]
  | cons p ps ih => simp [allOf, scope_both, ih]

theorem scope_anyOf (d : Nat) (ps : List SetFormula) :
    Scoped d (anyOf ps) ↔ ∀ p ∈ ps, Scoped d p := by
  induction ps with
  | nil => simp [anyOf, scope_falsity]
  | cons p ps ih => simp [anyOf, scope_either, ih]

theorem scope_empty {d a : Nat} (ha : a < d) : Scoped d (empty a) := by
  simp (disch := omega) only [empty, scope_every, scope_neg, scope_mem]
theorem scope_subset {d a b : Nat} (ha : a < d) (hb : b < d) : Scoped d (subset a b) := by
  simp (disch := omega) only [subset, scope_eachIn, scope_mem]

theorem scope_successor {d a b : Nat} (ha : a < d) (hb : b < d) : Scoped d (successor a b) := by
  simp (disch := omega) only [successor, scope_every, scope_iff, scope_either, scope_mem, scope_eq,
    and_self]

theorem scope_numeral (n : Nat) {d a : Nat} (ha : a < d) : Scoped d (numeral n a) := by
  induction n generalizing d a with
  | zero => exact scope_empty ha
  | succ n ih =>
    simp (disch := omega) only [numeral, scope_someSet, scope_both, ih, scope_successor, and_self]

theorem scope_pair {d a b p : Nat} (ha : a < d) (hb : b < d) (hp : p < d) :
    Scoped d (unorderedPair a b p) := by
  simp (disch := omega) only [unorderedPair, scope_every, scope_iff, scope_mem, scope_eq, scope_either,
    and_self]

theorem scope_orderedPair {d a b p : Nat} (ha : a < d) (hb : b < d) (hp : p < d) :
    Scoped d (orderedPair a b p) := by
  simp (disch := omega) only [orderedPair, scope_someSet, allOf, scope_both, scope_neg, scope_falsity,
    scope_pair, and_self]

theorem scope_graphValue {d f x y : Nat} (hf : f < d) (hx : x < d) (hy : y < d) :
    Scoped d (graphValue f x y) := by
  simp (disch := omega) only [graphValue, scope_someIn, scope_orderedPair]

theorem scope_functionOn {d f a : Nat} (hf : f < d) (ha : a < d) :
    Scoped d (functionOn f a) := by
  simp (disch := omega) only [functionOn, scope_both, scope_eachIn, scope_someIn, scope_someSet,
    scope_orderedPair, scope_graphValue, scope_every, scope_impl, scope_eq, and_self]

theorem scope_inductiveSet {d a : Nat} (ha : a < d) : Scoped d (inductiveSet a) := by
  simp (disch := omega) only [inductiveSet, scope_both, scope_someIn, scope_eachIn, scope_empty,
    scope_successor, and_self]

theorem scope_omega {d a : Nat} (ha : a < d) : Scoped d (omegaSet a) := by
  simp (disch := omega) only [omegaSet, scope_both, scope_every, scope_impl, scope_inductiveSet,
    scope_subset, and_self]

theorem scope_natObject {d a : Nat} (ha : a < d) : Scoped d (natObject a) := by
  simp (disch := omega) only [natObject, scope_someSet, scope_both, scope_omega, scope_mem, and_self]

theorem scope_addition {d a b c : Nat} (ha : a < d) (hb : b < d) (hc : c < d) :
    Scoped d (addition a b c) := by
  simp (disch := omega) only [addition, allOf, scope_both, scope_natObject, scope_someSet, scope_empty,
    scope_successor, scope_functionOn, scope_graphValue, scope_eachIn, scope_every, scope_impl,
    scope_neg, scope_falsity, and_self]

theorem scope_multiplication {d a b c : Nat} (ha : a < d) (hb : b < d) (hc : c < d) :
    Scoped d (multiplication a b c) := by
  simp (disch := omega) only [multiplication, allOf, scope_both, scope_natObject, scope_someSet,
    scope_empty, scope_successor, scope_functionOn, scope_graphValue, scope_eachIn, scope_every, scope_impl,
    scope_neg, scope_falsity, and_self, scope_addition]

theorem scope_bitCons (bit : Bool) {d x y : Nat} (hx : x < d) (hy : y < d) :
    Scoped d (bitCons bit x y) := by
  simp (disch := omega) only [bitCons, allOf, scope_both, scope_someSet, scope_numeral,
    scope_addition, scope_multiplication, scope_neg, scope_falsity, and_self]

end PalomarI3380.Logic.SetFormula
