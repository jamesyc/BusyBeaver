module
public import I3_334Support.SetTheory.Classes.ActiveRanks
public import I3_334Support.SetTheory.Classes.ModelSyntax
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)

theorem active_pairBound {a b : V} (ha : N.square.activePoint a) (hb : N.square.activePoint b) :
    N.square.activePoint (N.PairBound a b) :=
  N.active_canonical_power (N.active_canonical_power (N.active_union₂ ha hb))

theorem assignment_active {g a b : V} (h : Internal.FunctionInto N.mem g a b)
    (ha : N.square.activePoint a) (hb : N.square.activePoint b) :
    N.square.activePoint g :=
  active_subset N.laws (N.active_pairBound ha hb) (N.assignment_bound h)

theorem assignmentSpace_active {space arity stage : V} (h : ∀ env,
    N.mem env space ↔ Internal.FunctionInto N.mem env arity stage)
    (ha : N.square.activePoint arity) (hs : N.square.activePoint stage) :
    N.square.activePoint space :=
  active_subset N.laws (N.active_canonical_power (N.active_pairBound ha hs))
    (fun env he => (N.mem_power _ _).mpr (N.assignment_bound ((h env).mp he)))

private theorem valid_tag_in_omega {w a i t x y : V} (hw : Internal.Omega N.mem w)
    (valid : Internal.ValidRow N.mem a i t x y) : N.mem t w := by
  have ok (n : Nat) (h : Internal.Numeral N.mem n t) : N.mem t w :=
    ((N.numeral_def _ _).mp h).symm ▸ N.numeral_in_omega hw n
  rcases valid with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact ok _ h

theorem syntax_active {w arity count rows : V} (hw : Internal.Omega N.mem w)
    (wIn : N.square.activePoint w) (code : Internal.SyntaxCode N.mem w arity count rows) :
    N.square.activePoint rows := by
  let operandSpace := N.PairBound w w
  let rowSpace := N.PairBound w operandSpace
  let bound := N.PairBound w rowSpace
  have active := N.active_pairBound wIn (N.active_pairBound wIn (N.active_pairBound wIn wIn))
  apply active_subset N.laws (y := bound) active
  intro p hp
  obtain ⟨i, value, hi, pair⟩ := code.2.2.2.1.2 p hp
  obtain ⟨t, a, b, ⟨row, operands, earlier, tagPair, argsPair⟩, ha, hb, valid⟩ := code.2.2.2.2 i hi
  obtain ⟨_, _, unique⟩ := code.2.2.2.1.1 i hi
  have eq : value = row := (unique value ⟨p, hp, pair⟩).trans (unique row earlier).symm
  subst value
  have ops : N.mem operands operandSpace := by
    rw [(N.orderedPair_iff a b operands).mp argsPair]
    exact N.in_pairBound ha hb
  have ht := N.valid_tag_in_omega hw valid
  have rowIn : N.mem row rowSpace := by
    rw [(N.orderedPair_iff t operands row).mp tagPair]
    exact N.in_pairBound ht ops
  have iIn : N.mem i w := (N.omega_ordinal hw).transitive count code.2.1 i hi
  rw [(N.orderedPair_iff i row p).mp pair]
  exact N.in_pairBound iIn rowIn

end PalomarI3380.SquareRepresentation.NamedModel
