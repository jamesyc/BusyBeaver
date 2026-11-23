module
public import I3_334Support.SetTheory.Classes.TruthRecursion
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : SetContext M V)

theorem first_before {a i t x y : V} (valid : Internal.ValidRow N.mem a i t x y)
    (recursive : Internal.Numeral N.mem 2 t ∨ Internal.Numeral N.mem 3 t) : N.mem x i := by
  rcases valid with ⟨tag, hb, hc⟩ | ⟨tag, hb, hc⟩ | ⟨tag, bound⟩ | ⟨tag, bound, other⟩ | ⟨tag, hb, hc⟩
  all_goals first
    | exact bound
    | rcases recursive with h | h <;> have clash := N.numeral_not_clash tag h <;> omega

theorem second_before {a i t x y : V} (valid : Internal.ValidRow N.mem a i t x y)
    (recursive : Internal.Numeral N.mem 3 t ∨ Internal.Numeral N.mem 4 t) : N.mem y i := by
  rcases valid with ⟨tag, hb, hc⟩ | ⟨tag, hb, hc⟩ | ⟨tag, hb⟩ | ⟨tag, hb, bound⟩ | ⟨tag, hb, bound⟩
  all_goals first
    | exact bound
    | rcases recursive with h | h <;> have clash := N.numeral_not_clash tag h <;> omega

/-- A truth clause uses only earlier rows and well-typed assignments. -/
theorem rowTruth_congr {p q : V → V → Prop} {a s i t x y env : V}
    (valid : Internal.ValidRow N.mem a i t x y)
    (typed : Internal.FunctionInto N.mem env a s)
    (same : ∀ r, N.mem r i → ∀ e, Internal.FunctionInto N.mem e a s → (p r e ↔ q r e)) :
    Internal.RowTruth N.mem p a s env t x y ↔ Internal.RowTruth N.mem q a s env t x y := by
  unfold Internal.RowTruth
  refine or_congr Iff.rfl (or_congr Iff.rfl (or_congr ?_ (or_congr ?_ ?_)))
  · exact and_congr_right fun h => not_congr (same x (N.first_before valid (Or.inl h)) env typed)
  · exact and_congr_right fun h => and_congr (same x (N.first_before valid (Or.inr h)) env typed)
      (same y (N.second_before valid (Or.inl h)) env typed)
  · apply and_congr_right
    intro h
    apply exists_congr
    intro changed
    exact and_congr_right fun type => and_congr_right fun _ =>
      same y (N.second_before valid (Or.inr h)) changed type

theorem truthSet_rule {w a c r stage sat i env tag x y : V}
    (code : Internal.SyntaxCode N.mem w a c r) (table : Internal.TruthSet N.mem a c r stage sat)
    (hi : N.mem i c) (typed : Internal.FunctionInto N.mem env a stage)
    (atRow : Internal.RowAt N.mem r i tag x y) :
    Internal.At N.mem sat i env ↔
      Internal.RowTruth N.mem (Internal.At N.mem sat) a stage env tag x y := by
  obtain ⟨t, p, q, row, spec⟩ := table i hi env typed
  obtain ⟨eq₁, eq₂, eq₃⟩ := N.row_unique code.2.2.2.1 hi row atRow
  subst t
  subst p
  subst q
  exact spec

/-- Compute the truth table using set recursion on the model's syntax
index set. Its graph lies in the product bound for indices and
assignments, which is also available in the active domain. -/
theorem truthSet_exists {w arity count rows : V} (hw : Internal.Omega N.mem w)
    (code : Internal.SyntaxCode N.mem w arity count rows) (stage : V) :
    ∃ space sat, (∀ env, N.mem env space ↔ Internal.FunctionInto N.mem env arity stage) ∧
      N.Subset sat (N.PairBound count space) ∧ Internal.TruthSet N.mem arity count rows stage sat := by
  obtain ⟨space, context⟩ := N.assignment_space arity stage
  let data : TruthInput V := ⟨space,rows,arity,stage⟩
  have countOrdinal := (N.omega_ordinal hw).of_mem N code.2.1
  obtain ⟨family, computed⟩ := (N.truthRecursor data countOrdinal).solution_exists
  let bound := N.PairBound count space
  have hSpec (i env : V) (h : N.FamilyTruth family i env) : N.mem i count ∧ N.mem env space := by
    obtain ⟨s, hs, member⟩ := h
    have hi := SetRecursion.at_domain computed.functionOn hs
    obtain ⟨past, _, values⟩ := N.familyTruth_value computed hi
    exact ⟨hi, ((values env).mp ⟨s,hs,member⟩).1⟩
  have pair := Definable.orderedPair (N := N) (n := 4) (i := 1) (j := 0) (k := 2)
    (by decide) (by decide) (by decide)
  have truth := N.familyTruth_definable (n := 4) (i := 3) (j := 1) (k := 0)
    (by decide) (by decide) (by decide)
  obtain ⟨sat, spec⟩ := N.separate [] (Definable.ex (Definable.ex (pair.and truth))) bound family
  have meanings (i env : V) : Internal.At N.mem sat i env ↔ N.FamilyTruth family i env := by
    rw [N.at_pair, spec]
    constructor
    · rintro ⟨_, x, y, code, yes⟩
      change Internal.OrderedPair N.mem x y (N.orderedPair i env) at code
      change N.FamilyTruth family x y at yes
      obtain ⟨sameX, sameY⟩ := Internal.orderedPair_injective code (N.orderedPair_intro i env)
      exact sameX ▸ sameY ▸ yes
    · intro h
      exact ⟨N.in_pairBound (hSpec i env h).1 (hSpec i env h).2, i, env,
        N.orderedPair_intro _ _, h⟩
  refine ⟨space, sat, context, (fun p hp => ((spec p).mp hp).1), ?_⟩
  intro i hi env typed
  obtain ⟨tag, x, y, atRow, hx, hy, valid⟩ := code.2.2.2.2 i hi
  obtain ⟨previous, restrict, outputs⟩ := N.familyTruth_value computed hi
  refine ⟨tag, x, y, atRow, (meanings i env).trans ((outputs env).trans ?_)⟩
  have reduceLayer :
      N.TruthLayer rows arity stage i previous env ↔
        Internal.RowTruth N.mem (N.FamilyTruth previous) arity stage env tag x y := by
    constructor
    · rintro ⟨t, a, b, row, truth⟩
      obtain ⟨eq₁, eq₂, eq₃⟩ := N.row_unique code.2.2.2.1 hi row atRow
      subst t
      subst a
      subst b
      exact truth
    · exact fun h => ⟨tag, x, y, atRow, h⟩
  have strip : (N.mem env space ∧ N.TruthLayer rows arity stage i previous env) ↔
      N.TruthLayer rows arity stage i previous env :=
    ⟨And.right, fun h => ⟨(context env).mpr typed, h⟩⟩
  exact strip.trans (reduceLayer.trans (N.rowTruth_congr valid typed fun row before e _ =>
    (N.familyTruth_restrict restrict before).trans (meanings row e).symm))


end PalomarI3380.SquareRepresentation.SetContext
