module
public import I0451.Logic.ZFModel
public import Foundation.FirstOrder.SetTheory.Recursion.Blueprint

/-! Collection in arbitrary ZF models from Replacement and Foundation.
Each input selects an ordinal level by its least possible witness rank.
Replacement collects these ordinals without choosing any witnesses. -/
@[expose] public section
namespace I0451.Logic.ZFModel

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open FFL.FirstOrder.SetTheory.Replacement

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def levelStep (f : V) : V :=
  ⋃ˢ repl (fun x : V => ℘ x) (by definability) (range f)

theorem levelStep_defined : ℒₛₑₜ-function₁[V] (levelStep : V → V) := by
  unfold levelStep
  definability

noncomputable def cumulativeLevel (a : V) : V :=
  transfiniteRec levelStep levelStep_defined a

@[definability] theorem cumulativeLevel_defined : ℒₛₑₜ-function₁[V] (cumulativeLevel : V → V) :=
  transfiniteRec_definable levelStep_defined

theorem mem_cumulativeLevel {z : V} (a : Ordinal V) :
    z ∈ cumulativeLevel (a : V) ↔ ∃ b ∈ (a : V), z ⊆ cumulativeLevel b := by
  unfold cumulativeLevel
  rw [transfiniteRec_spec levelStep levelStep_defined a]
  unfold levelStep
  simp only [mem_sUnion_iff, repl_spec, mem_range_iff]
  constructor
  · rintro ⟨w, ⟨r, ⟨u, b, hba, eq⟩, rfl⟩, hz⟩
    have value := kpair_inj eq
    rw [value.2] at hz
    exact ⟨b, hba, mem_power_iff.mp hz⟩
  · rintro ⟨b, hb, hz⟩
    refine ⟨_, ⟨_, ⟨b, b, hb, rfl⟩, rfl⟩, mem_power_iff.mpr hz⟩

theorem cumulativeLevel_mono {a b : Ordinal V} (le : a ≤ b) :
    cumulativeLevel (a : V) ⊆ cumulativeLevel (b : V) := by
  intro z mem
  obtain ⟨c, hc, hz⟩ := (mem_cumulativeLevel a).mp mem
  exact (mem_cumulativeLevel b).mpr ⟨c, le c hc, hz⟩

def levelStepDef : SetTheorySemisentence 2 :=
  f“result history. ∀ z, z ∈ result ↔ ∃ a ∈ !range.dfn history, z ⊆ a”

theorem levelStep_defines :
    DefinedFunction (fun v : Fin 1 → V => levelStep (v 0)) levelStepDef := by
  refine .mk fun v => ?_
  have membership (z f : V) : z ∈ levelStep f ↔ ∃ a ∈ range f, z ⊆ a := by
    simp only [levelStep, mem_sUnion_iff, repl_spec]
    exact ⟨fun ⟨_, ⟨a, ha, rfl⟩, hz⟩ => ⟨a, ha, mem_power_iff.mp hz⟩,
      fun ⟨a, ha, hz⟩ => ⟨℘ a, ⟨a, ha, rfl⟩, mem_power_iff.mpr hz⟩⟩
  simp [levelStepDef, range.defined.iff]
  change _ ↔ v 0 = levelStep (v 1)
  rw [mem_ext_iff]
  simp [membership]

def cumulativeLevelBlueprint : Recursion.Blueprint 0 where
  graph := levelStepDef

noncomputable def cumulativeLevelConstruction : Recursion.Construction V cumulativeLevelBlueprint where
  map := fun _ => levelStep
  map_defined := levelStep_defines

def cumulativeLevelDef : SetTheorySemisentence 2 := cumulativeLevelBlueprint.result_dfn

theorem cumulativeLevel_defines :
    DefinedFunction (fun v : Fin 1 → V => cumulativeLevel (v 0)) cumulativeLevelDef := by
  refine .mk fun v => ?_
  let c := cumulativeLevelConstruction (V := V)
  let noParameters : Fin 0 → V := Fin.elim0
  have graph := c.result_defined_iff v
  have agrees : c.result (v ·.succ.succ) (v 1) = cumulativeLevel (v 1) := by
    have params : (v ·.succ.succ) = noParameters := Subsingleton.elim _ _
    rw [params]
    by_cases ord : IsOrdinal (v 1)
    · let a := ord.toOrdinal
      obtain ⟨f, attempt, length, entry⟩ := (c.result_spec noParameters (v 1)).1 ord
      have atIndex : v 1 ∈ lh f := length.symm ▸ mem_succ_self _
      have value := (attempt.2 _ atIndex _).mp entry
      have cut : f ↾ (v 1) = replAttemptOrEmpty (V := V) levelStep levelStep_defined a :=
        IsAttempt.isAttempt_restrict_eq_of_le
          (α := a.succ) (β := a)
          (fun x hx => mem_succ_iff.mpr (.inr hx)) attempt
          (replAttemptOrEmpty_aux levelStep levelStep_defined a) length
          (lh_replAttemptOrEmpty_eq levelStep levelStep_defined a)
      unfold cumulativeLevel transfiniteRec
      rw [ite_eq_left ord]
      exact value.trans (congrArg levelStep cut)
    · rw [c.result_not_isOrdinal noParameters _ ord,
        cumulativeLevel, transfiniteRec_spec_of_not_isOrdinal _ _ ord]
  change cumulativeLevelDef.Evalb v ↔ v 0 = cumulativeLevel (v 1)
  exact graph.trans (by rw [agrees])

attribute [local irreducible] cumulativeLevel

private def WitnessLevel (R : V → V → Prop) (x a : V) : Prop :=
  ∃ y ∈ cumulativeLevel a, R x y

private def LeastLevel (R : V → V → Prop) (x a : V) : Prop :=
  IsOrdinal a ∧ WitnessLevel R x a ∧
    ∀ b, IsOrdinal b → WitnessLevel R x b → a ⊆ b

private theorem witnessLevel_defined (R : V → V → Prop) (defR : ℒₛₑₜ-relation R) (x : V) :
    ℒₛₑₜ-predicate (WitnessLevel R x) := by
  unfold WitnessLevel
  have levels := cumulativeLevel_defined (V := V)
  definability

private theorem leastLevel_defined (R : V → V → Prop) (defR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-relation (LeastLevel R) := by
  unfold LeastLevel WitnessLevel
  have levels := cumulativeLevel_defined (V := V)
  definability

private theorem leastLevel_unique {R : V → V → Prop} {x : V}
    (defR : ℒₛₑₜ-relation R) (small : ∃ a : Ordinal V, WitnessLevel R x a) :
    ∃! a : V, LeastLevel R x a := by
  obtain ⟨a, yes, least⟩ := exists_minimal (WitnessLevel R x) (witnessLevel_defined R defR x) small
  have best : LeastLevel R x a :=
    ⟨a.ordinal, yes, fun b ordinal known => least ordinal.toOrdinal known⟩
  refine ⟨a, best, fun b other => ?_⟩
  exact mem_ext_iff.mpr fun y => ⟨other.2.2 a a.ordinal yes y, best.2.2 b other.1 other.2.1 y⟩

/-- Once a witness for each input occurs in some level, a common level
bounds all of those witnesses. -/
private theorem witnessLevel_bounded (R : V → V → Prop) (defR : ℒₛₑₜ-relation R) (A : V)
    (small : ∀ x ∈ A, ∃ a : Ordinal V, WitnessLevel R x a) :
    ∃ a : Ordinal V, ∀ x ∈ A, WitnessLevel R x a := by
  obtain ⟨ranks, spec⟩ := replacement_rel_exists_of_mem_existsUnique A
    (LeastLevel R) (fun x hx => leastLevel_unique defR (small x hx)) (leastLevel_defined R defR)
  have ranges (b : V) (hb : b ∈ ranks) : IsOrdinal b := by
    obtain ⟨x, _, least⟩ := (spec b).mp hb
    exact least.1
  let a : Ordinal V := (IsOrdinal.sUnion ranges).toOrdinal
  refine ⟨a, fun x hx => ?_⟩
  obtain ⟨b, least, _⟩ := leastLevel_unique defR (small x hx)
  have ranksMem : b ∈ ranks := (spec b).mpr ⟨x, hx, least⟩
  have below : least.1.toOrdinal ≤ a := subset_sUnion_of_mem ranksMem
  obtain ⟨y, found, relation⟩ := least.2.1
  exact ⟨y, cumulativeLevel_mono below y found, relation⟩

private def HasLevel (z : V) : Prop := ∃ a : Ordinal V, z ∈ cumulativeLevel (a : V)

private theorem hasLevel_defined : ℒₛₑₜ-predicate[V] (HasLevel : V → Prop) := by
  have found : ℒₛₑₜ-predicate (fun z : V => ∃ a : V, IsOrdinal a ∧ z ∈ cumulativeLevel a) := by
    have levels := cumulativeLevel_defined (V := V)
    definability
  exact found.of_iff fun z => ⟨fun ⟨a, mem⟩ => ⟨a, a.ordinal, mem⟩,
    fun ⟨a, ordinal, mem⟩ => ⟨ordinal.toOrdinal, mem⟩⟩

theorem cumulativeLevel_covers (z : V) : ∃ a : Ordinal V, z ∈ cumulativeLevel (a : V) := by
  change HasLevel z
  by_contra missing
  let T := TransitiveClosure.transClosure ({z} : V)
  let bad := sep T (fun z => ¬HasLevel z) (by
    have defined := hasLevel_defined (V := V)
    definability)
  have zIn : z ∈ T := TransitiveClosure.self_subset_transClosure z (by simp)
  let : IsNonempty bad := ⟨⟨z, mem_sep_iff.mpr ⟨zIn, missing⟩⟩⟩
  obtain ⟨w, badMem, minimal⟩ := FFL.FirstOrder.SetTheory.foundation bad
  have current : w ∈ T ∧ ¬HasLevel w := mem_sep_iff.mp badMem
  have localCover (x : V) (hx : x ∈ w) : HasLevel x := by
    by_contra none
    have transitive : IsTransitive T := inferInstance
    have member : x ∈ bad := mem_sep_iff.mpr ⟨transitive.transitive w current.1 x hx, none⟩
    exact minimal x member hx
  obtain ⟨alpha, level⟩ := witnessLevel_bounded (fun (x y : V) => x = y) (by definability) w
    (fun x hx => by
      obtain ⟨a, mem⟩ := localCover x hx
      exact ⟨a, x, mem, rfl⟩)
  have below : w ⊆ cumulativeLevel alpha := by
    intro x hx
    obtain ⟨_, member, rfl⟩ := level x hx
    exact member
  have next : (alpha : V) ∈ (alpha.succ : V) := by
    change alpha < alpha.succ
    simp
  exact current.2 ⟨alpha.succ, (mem_cumulativeLevel alpha.succ).mpr ⟨alpha, next, below⟩⟩

theorem boundedCollection_of_zf : BoundedCollection (V := V) := by
  intro R defR A
  let definedInputs := sep A (fun x => ∃ y, R x y) (by definability)
  have small (x : V) (hx : x ∈ definedInputs) : ∃ a : Ordinal V, WitnessLevel R x a := by
    obtain ⟨_, y, rel⟩ := mem_sep_iff.mp hx
    obtain ⟨a, mem⟩ := cumulativeLevel_covers y
    exact ⟨a, y, mem, rel⟩
  obtain ⟨a, bounded⟩ := witnessLevel_bounded R defR definedInputs small
  exact ⟨cumulativeLevel a, fun x hx has => bounded x (mem_sep_iff.mpr ⟨hx, has⟩)⟩

end I0451.Logic.ZFModel
