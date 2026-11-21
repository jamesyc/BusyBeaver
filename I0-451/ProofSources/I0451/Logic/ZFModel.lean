module
public import I0451.Logic.SetSyntax
public import I0451.Logic.SetSentences
public import Foundation.FirstOrder.SetTheory.TransitiveClosure

/-! Set operations required by the source calculus. The container is
constructed inside each model using its own omega iteration. -/
@[expose] public section
namespace I0451.Logic.ZFModel

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def powerBlueprint : NaturalNumberRec.Blueprint 1 where
  zero := “y x. y = x”
  succ := “y prev i x. !power.dfn y prev”

noncomputable def powerIteration : NaturalNumberRec.Construction V powerBlueprint where
  zero := fun v => v 0
  succ := fun _ _ x => ℘ x
  zero_defined := ⟨fun v => by simp [powerBlueprint]⟩
  succ_defined := ⟨fun v => power.defined.eval_iff ![v 0, v 1]⟩

def powerImageBlueprint : Repl.Blueprint 1 where
  graph := powerBlueprint.resultDef

noncomputable def powerImage : Repl.Construction V powerImageBlueprint where
  map := powerIteration.result
  map_defined := powerIteration.result_defined

noncomputable def powerHull (x : V) : V := ⋃ˢ powerImage.result ![x] (ω : V)

theorem mem_powerHull_iff (x z : V) :
    z ∈ powerHull x ↔ ∃ n ∈ (ω : V), z ∈ powerIteration.result ![x] n := by
  unfold powerHull
  simp only [mem_sUnion_iff, Repl.Construction.mem_result]
  constructor
  · rintro ⟨_, ⟨n, hn, rfl⟩, hz⟩
    exact ⟨n, hn, hz⟩
  · rintro ⟨n, hn, hz⟩
    exact ⟨_, ⟨n, hn, rfl⟩, hz⟩

theorem power_transitive {x : V} (hx : IsTransitive x) : IsTransitive (℘ x) := by
  constructor
  intro y hy z hz
  apply mem_power_iff.mpr
  have zy : z ∈ x := mem_power_iff.mp hy z hz
  exact hx.transitive z zy

theorem powerStage_defined (x : V) :
    ℒₛₑₜ-function₁[V] (powerIteration.result ![x]) := by
  let terms : Fin 3 → Semiterm ℒₛₑₜ V 2 := ![#0, #1, &x]
  refine ⟨(Rew.embSubsts terms) ▹ powerBlueprint.resultDef, fun v => ?_⟩
  rw [Semiformula.eval_embSubsts]
  have args : (Semiterm.val (L := ℒₛₑₜ) v id ∘ terms) = ![v 0, v 1, x] := by
    funext i
    have small : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    rcases small i with rfl | rfl | rfl <;> rfl
  rw [args]
  have one : Fin.succ (0 : Fin 1) = (1 : Fin 2) := by decide
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.vec_single_eq_const, one] using
    powerIteration.result_defined.iff ![v 0, v 1, x]

theorem stage_transitive {x n : V} (hx : IsTransitive x) (hn : n ∈ (ω : V)) :
    IsTransitive (powerIteration.result ![x] n) := by
  apply naturalNumber_induction (fun n => IsTransitive (powerIteration.result ![x] n)) ?_ ?_ ?_ n hn
  · have graph := powerStage_defined x
    definability
  · rw [powerIteration.result_zero]
    exact hx
  · intro k hk ih
    rw [powerIteration.result_succ ![x] hk]
    exact power_transitive ih

theorem powerHull_transitive {x : V} (hx : IsTransitive x) : IsTransitive (powerHull x) := by
  constructor
  intro y hy z hz
  obtain ⟨n, hn, h⟩ := (mem_powerHull_iff x y).mp hy
  exact (mem_powerHull_iff x z).mpr ⟨n, hn, (stage_transitive hx hn).transitive y h z hz⟩

theorem power_mem_hull {x y : V} (hx : IsTransitive x) (hy : y ∈ powerHull x) :
    ℘ y ∈ powerHull x := by
  obtain ⟨n, hn, yn⟩ := (mem_powerHull_iff x y).mp hy
  let stage := powerIteration.result ![x] n
  have subset : ℘ y ⊆ ℘ stage := by
    intro z hz
    apply mem_power_iff.mpr
    intro u hu
    exact (stage_transitive hx hn).transitive y yn u ((mem_power_iff.mp hz) u hu)
  have mem : ℘ y ∈ ℘ (℘ stage) := mem_power_iff.mpr subset
  refine (mem_powerHull_iff x _).mpr ⟨succ (succ n), ω_succ_closed (ω_succ_closed hn), ?_⟩
  rw [powerIteration.result_succ ![x] (ω_succ_closed hn), powerIteration.result_succ ![x] hn]
  exact mem

theorem container (p : V) :
    ∃ d, p ∈ d ∧ ∀ y ∈ d,
      (∃ w ∈ d, ∀ z, Subset (fun a b : V => a ∈ b) z y → z ∈ w) ∧
        Subset (fun a b : V => a ∈ b) y d := by
  let trans := TransitiveClosure.transClosure ({p} : V)
  have htrans : IsTransitive trans := inferInstance
  have seed : p ∈ trans := TransitiveClosure.self_subset_transClosure p (by simp)
  let d := powerHull trans
  have belongs : p ∈ d := (mem_powerHull_iff trans p).mpr
    ⟨0, zero_mem_ω, powerIteration.result_zero ![trans] ▸ seed⟩
  refine ⟨d, belongs, fun y hy => ⟨?_, (powerHull_transitive htrans).transitive y hy⟩⟩
  exact ⟨℘ y, power_mem_hull htrans hy, fun z hz => mem_power_iff.mpr hz⟩

/-- Bounded Collection for every first-order definable binary relation. -/
def BoundedCollection : Prop :=
  ∀ (R : V → V → Prop), (ℒₛₑₜ-relation R) → ∀ A : V, ∃ C : V,
    ∀ x ∈ A, (∃ y, R x y) → ∃ y ∈ C, R x y

theorem collection_global (collect : BoundedCollection (V := V))
    (R : V → V → Prop) (definable : ℒₛₑₜ-relation R) (A : V) :
    ∃ C : V, (∀ x y, x ∈ A → R x y → ∃ z, R x z ∧ z ∈ C) ∧
      (∀ y, y ∈ C → ∃ x, R x y) := by
  obtain ⟨bound, hb⟩ := collect R definable A
  let P : V → Prop := fun y => ∃ x ∈ A, R x y
  have hP : ℒₛₑₜ-predicate P := by unfold P; definability
  let C := sep bound P hP
  have members (y : V) : y ∈ C ↔ y ∈ bound ∧ P y := mem_sep_iff
  refine ⟨C, ?_, fun y hy => ?_⟩
  · intro x y hx hxy
    obtain ⟨z, hz, rz⟩ := hb x hx ⟨y, hxy⟩
    exact ⟨z, rz, (members z).mpr ⟨hz, x, hx, rz⟩⟩
  · obtain ⟨x, _, h⟩ := (members y).mp hy |>.2
    exact ⟨x, h⟩

theorem bundleModel (collect : BoundedCollection (V := V)) :
    BundleModel (fun x y : V => x ∈ y) where
  irrefl := mem_irrefl
  extensionality := fun _ _ h => mem_ext_iff.mpr h
  empty := ⟨∅, fun x => by simp⟩
  container := container
  collect := fun a b code s domain =>
    collection_global collect _ (SetSyntax.definable_code_relation a b code s) domain

theorem foundation : SetSentences.Foundation (fun x y : V => x ∈ y) := by
  intro a nonempty
  let : IsNonempty a := ⟨nonempty⟩
  obtain ⟨x, hx, hm⟩ := FFL.FirstOrder.SetTheory.foundation a
  exact ⟨x, hx, fun y hy hya => hm y hya hy⟩

theorem setOperations : AssignmentCode.SetOperations (fun x y : V => x ∈ y) where
  extensionality := fun _ _ h => mem_ext_iff.mpr h
  unorderedPair := fun x y => ⟨{x,y}, fun z => by simp⟩
  update := by
    intro g old new
    let P : V → Prop := fun p => p ≠ old
    have hP : ℒₛₑₜ-predicate P := by unfold P; definability
    refine ⟨insert new (sep g P hP), fun p => ?_⟩
    simp [P, or_comm]

end I0451.Logic.ZFModel
