module
public import I0451.Logic.AssignmentTuples
public import I0451.Logic.SetSatisfaction

/-! Elementarity of a set-coded map for internally finite formulas. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode I0451.Logic.SetFormulaPrograms

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def PreservesSatisfaction (d target j : V) : Prop :=
  ∀ word, IsFormulaWord word → ∀ i ∈ lh word,
    ∀ args, Tuple d args (nodeArity word i) → ∀ images, ReadsTuple j args images →
      (Satisfies d word i args ↔ Satisfies target word i images)

def CodedElementary (d j : V) : Prop :=
  j ∈ assignments d ∧ PreservesSatisfaction d d j

theorem identity_readsTuple {d args n : V} (tuple : Tuple d args n) :
    ReadsTuple (identity d) args args := by
  refine ⟨tuple.1, rfl, fun i within => ?_⟩
  have labels := tuple.2.2 _ (mem_range_iff.mpr ⟨i, tuple.1.znth within⟩)
  exact (diagonal_at d _ _).mpr ⟨labels, rfl⟩

def preservesSatisfactionDef : SetTheorySemisentence 3 :=
  “D target j. ∀ word, !formulaWordDef word →
    ∀ length, !lh.dfn length word → ∀ index ∈ length,
      ∀ arity, !arityDef arity word index → ∀ args, !tupleDef D args arity →
        ∀ images, !readsTupleDef j args images →
          (!satisfiesDef D word index args ↔ !satisfiesDef target word index images)”

theorem preservesSatisfaction_defines :
    Defined (fun v : Fin 3 → V => PreservesSatisfaction (v 0) (v 1) (v 2)) preservesSatisfactionDef :=
  .mk fun v => by
    simp [preservesSatisfactionDef, PreservesSatisfaction, formulaWord_defines.iff,
      lh.defined.iff, arity_defines.iff, tuple_defines.iff, readsTuple_defines.iff, satisfies_defines.iff]

def codedElementaryDef : SetTheorySemisentence 2 :=
  “D j. !mapDef j D ∧ !preservesSatisfactionDef D D j”

theorem codedElementary_defines :
    Defined (fun v : Fin 2 → V => CodedElementary (v 0) (v 1)) codedElementaryDef :=
  .mk fun v => by
    have map : Defined (fun env : Fin 2 → V => IsMap (fun a b : V => a ∈ b) (env 1) (env 0)) mapDef :=
      .mk fun env => by rw [Matrix.fun_eq_vec_two env]; exact eval_mapDef _ _
    simp [codedElementaryDef, CodedElementary, map.iff, mem_universe, preservesSatisfaction_defines.iff]

end I0451.Logic.SetAssignments
