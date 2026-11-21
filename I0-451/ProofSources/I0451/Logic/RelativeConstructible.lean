module
public import I0451.Logic.SetSatisfaction
public import Foundation.FirstOrder.SetTheory.Recursion.Blueprint
public import Foundation.FirstOrder.SetTheory.TransitiveClosure

/-! Definable subsets and the relative constructible hierarchy.
The defining formulas use the checked satisfaction predicate for
internally finite first-order formulas. -/
@[expose] public section
namespace I0451.Logic.ZFModel

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.Logic.SetFormulaPrograms

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def DefinedSubset (x d : V) : Prop :=
  ∃ word, IsFormulaWord word ∧ ∃ index ∈ lh word, ∃ parameters,
    parameters ∈ tupleUniverse d ∧ nodeArity word index = succ (lh parameters) ∧
      ∀ a ∈ d, a ∈ x ↔ Satisfies d word index (parameters ⁀' a)

def definedSubsetDef : SetTheorySemisentence 2 :=
  f“x d. ∃ word, !formulaWordDef word ∧ ∃ index ∈ !lh.dfn word, ∃ parameters,
    !tupleUniverseDef d parameters ∧ !arityDef (!succ.dfn (!lh.dfn parameters)) word index ∧
      ∀ a ∈ d, a ∈ x ↔ !satisfiesDef d word index (!seqCons.dfn parameters a)”

theorem definedSubset_defines :
    Defined (fun v : Fin 2 → V => DefinedSubset (v 0) (v 1)) definedSubsetDef :=
  .mk fun v => by
    simp [definedSubsetDef, DefinedSubset, formulaWord_defines.iff, tupleUniverse_defines.iff,
      arity_defines.iff, satisfies_defines.iff, lh.defined.iff, seqCons.defined.iff, succ.defined.iff, eq_comm]

noncomputable def definableSubsets (d : V) : V :=
  sep (℘ d) (DefinedSubset · d) (by
    let slots : Fin 2 → (Fin 1 → V) → V := ![fun v => v 0, fun _ => d]
    have each (i : Fin 2) : Language.DefinableFunction ℒₛₑₜ (slots i) := by
      have cases : i = 0 ∨ i = 1 := by omega
      rcases cases with rfl | rfl <;> dsimp [slots] <;> definability
    exact Language.Definable.substitution (f := slots) definedSubset_defines.to_definable each)

theorem mem_definableSubsets (x d : V) :
    x ∈ definableSubsets d ↔ x ⊆ d ∧ DefinedSubset x d := by
  rw [definableSubsets, mem_sep_iff, mem_power_iff]

def definableSubsetsDef : SetTheorySemisentence 2 :=
  “result d. ∀ x, x ∈ result ↔ x ⊆ d ∧ !definedSubsetDef x d”

theorem definableSubsets_defines :
    DefinedFunction (fun v : Fin 1 → V => definableSubsets (v 0)) definableSubsetsDef :=
  .mk fun v => by
    simp [definableSubsetsDef, definedSubset_defines.iff, ← mem_definableSubsets, mem_ext_iff]

noncomputable def constructibleStep (base history : V) : V := by
  classical
  exact if lh history = ∅ then base
    else if lh history = succ (⋃ˢ lh history) then definableSubsets (znth history (⋃ˢ lh history))
    else ⋃ˢ range history

def constructibleStepDef : SetTheorySemisentence 3 :=
  “result history base. ∃ length pred,
    !lh.dfn length history ∧ !sUnion.dfn pred length ∧
      ((!isEmpty length ∧ result = base) ∨
       (¬!isEmpty length ∧ !succ.dfn length pred ∧
        ∃ prior, !znth.dfn prior history pred ∧ !definableSubsetsDef result prior) ∨
       (¬!isEmpty length ∧ ¬!succ.dfn length pred ∧
        ∃ values, !range.dfn values history ∧ !sUnion.dfn result values))”

attribute [local irreducible] definableSubsetsDef definableSubsets definedSubsetDef

theorem constructibleStep_defines :
    DefinedFunction (fun v : Fin 2 → V => constructibleStep (v 1) (v 0)) constructibleStepDef :=
  .mk fun v => by
    have empty : Defined (fun e : Fin 1 → V => e 0 = ∅) isEmpty := by
      refine .mk fun e => ?_
      simpa [isEmpty, FFL.FirstOrder.SetTheory.IsEmpty] using (isEmpty_iff_eq_empty (x := e 0))
    have expanded :
        constructibleStepDef.Evalb v ↔
          (lh (v 1) = ∅ ∧ v 0 = v 2) ∨
          (lh (v 1) ≠ ∅ ∧ lh (v 1) = succ (⋃ˢ lh (v 1)) ∧
            v 0 = definableSubsets (znth (v 1) (⋃ˢ lh (v 1)))) ∨
          (lh (v 1) ≠ ∅ ∧ lh (v 1) ≠ succ (⋃ˢ lh (v 1)) ∧ v 0 = ⋃ˢ range (v 1)) := by
      simp [constructibleStepDef, empty.iff, lh.defined.iff, succ.defined.iff,
        sUnion.defined.iff, range.defined.iff, znth.defined.iff, definableSubsets_defines.iff]
    rw [expanded]
    change _ ↔ v 0 = constructibleStep (v 2) (v 1)
    unfold constructibleStep
    by_cases zero : lh (v 1) = ∅
    · rw [ite_eq_left zero]
      exact ⟨fun h => h.elim And.right (fun h => h.elim (fun p => (p.1 zero).elim) (fun p => (p.1 zero).elim)),
        fun result => .inl ⟨zero, result⟩⟩
    · rw [ite_eq_right zero]
      by_cases successor : lh (v 1) = succ (⋃ˢ lh (v 1))
      · rw [ite_eq_left successor]
        exact ⟨fun h => h.elim (fun p => (zero p.1).elim)
          (fun h => h.elim (fun p => p.2.2) (fun p => (p.2.1 successor).elim)),
          fun result => .inr (.inl ⟨zero, successor, result⟩)⟩
      · rw [ite_eq_right successor]
        exact ⟨fun h => h.elim (fun p => (zero p.1).elim)
          (fun h => h.elim (fun p => (successor p.2.1).elim) (fun p => p.2.2)),
          fun result => .inr (.inr ⟨zero, successor, result⟩)⟩

def relativeConstructibleBlueprint : Recursion.Blueprint 1 where
  graph := constructibleStepDef

noncomputable def relativeConstructibleIteration : Recursion.Construction V relativeConstructibleBlueprint where
  map := fun base history => constructibleStep (base 0) history
  map_defined := constructibleStep_defines

noncomputable def relativeConstructibleStage (X α : V) : V :=
  relativeConstructibleIteration.result ![TransitiveClosure.transClosure ({X} : V)] α

def relativeConstructibleStageDef : SetTheorySemisentence 3 :=
  “stage X α. ∃ seed base, !singleton.dfn seed X ∧ !TransitiveClosure.transClosure.dfn base seed ∧
    !relativeConstructibleBlueprint.result_dfn stage α base”

theorem relativeConstructibleStage_defines :
    DefinedFunction (fun v : Fin 2 → V => relativeConstructibleStage (v 0) (v 1)) relativeConstructibleStageDef :=
  .mk fun v => by
    simp [relativeConstructibleStageDef, relativeConstructibleStage,
      (relativeConstructibleIteration (V := V)).result_defined_iff,
      TransitiveClosure.transClosure.defined.iff, singleton.defined.iff, Matrix.vec_single_eq_const]

def RelativeConstructible (X x : V) : Prop :=
  ∃ α, IsOrdinal α ∧ x ∈ relativeConstructibleStage X α

def relativeConstructibleDef : SetTheorySemisentence 2 :=
  f“X x. ∃ α, !IsOrdinal.dfn α ∧ x ∈ !relativeConstructibleStageDef X α”

theorem relativeConstructible_defines :
    Defined (fun v : Fin 2 → V => RelativeConstructible (v 0) (v 1)) relativeConstructibleDef :=
  .mk fun v => by
    simp [relativeConstructibleDef, RelativeConstructible, IsOrdinal.defined.iff,
      relativeConstructibleStage_defines.iff]

end I0451.Logic.ZFModel
