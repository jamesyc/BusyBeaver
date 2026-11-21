module
public import I0451.Logic.ZFModel

/-! The actual assignment universe and identity graph exist inside
every ZF model. These sets supply the parameters of the compressed
embedding sentence. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

theorem kpair_is_pair (x y : V) : Pair E (kpair x y) x y := by
  intro z
  simp only [kpair, mem_insert, mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · simp
    · simp
  · rintro ⟨contains, bounded⟩
    by_cases hasY : y ∈ z
    · right
      apply mem_ext_iff.mpr
      intro a
      simpa using ⟨bounded a, fun h : a = x ∨ a = y => h.elim (· ▸ contains) (· ▸ hasY)⟩
    · left
      apply mem_ext_iff.mpr
      intro a
      simp only [mem_singleton_iff]
      exact ⟨fun h => (bounded a h).resolve_right (fun eq => hasY (eq ▸ h)), (· ▸ contains)⟩

theorem pair_iff_kpair (p x y : V) : Pair E p x y ↔ p = kpair x y := by
  constructor
  · intro spec
    apply mem_ext_iff.mpr
    intro z
    exact (spec z).trans ((kpair_is_pair x y) z).symm
  · rintro rfl
    exact kpair_is_pair x y

theorem at_iff_mem_kpair (g x y : V) : At E g x y ↔ kpair x y ∈ g := by
  simp [At, pair_iff_kpair]

def atDef : SetTheorySemisentence 3 := “g x y. ∃ p ∈ g, !kpair.dfn p x y”

@[simp] theorem eval_atDef (g x y : V) : atDef.Evalb ![g,x,y] ↔ At E g x y := by
  simp [atDef, kpair.defined.iff, at_iff_mem_kpair]

theorem at_defines : Defined (fun v : Fin 3 → V => At E (v 0) (v 1) (v 2)) atDef :=
  .mk (IsDefinedBy.of_vec_three eval_atDef)

theorem At_definable : ℒₛₑₜ-relation₃[V] (At E) :=
  at_defines.to_definable

def mapDef : SetTheorySemisentence 2 :=
  “g D. (∀ p ∈ g, ∀ s ∈ p, ∀ x ∈ s, x ∈ D) ∧
    (∀ x ∈ D, ∃! y, ∃ p ∈ g, !kpair.dfn p x y)”

theorem eval_mapDef (g d : V) : mapDef.Evalb ![g, d] ↔ IsMap E d g := by
  simp [mapDef, kpair.defined.iff, IsMap, Bounded, at_iff_mem_kpair, Domain,
    ExistsUnique, eq_comm]

theorem map_predicate (d : V) : ℒₛₑₜ-predicate (IsMap E d) := by
  refine ⟨(Rew.embSubsts ![#0, &d]) ▹ mapDef, fun env => ?_⟩
  rw [Semiformula.eval_embSubsts]
  have lookup : (Semiterm.val (L := ℒₛₑₜ) env id ∘ ![#0, &d]) = ![env 0, d] := by
    funext j
    have eq : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    rcases eq j with rfl | rfl <;> rfl
  rw [lookup]
  exact eval_mapDef (env 0) d

noncomputable def assignments (d : V) : V :=
  sep (℘ (℘ (℘ d))) (IsMap E d) (map_predicate d)

theorem mem_universe (d g : V) : g ∈ assignments d ↔ IsMap E d g := by
  rw [assignments, mem_sep_iff]
  constructor
  · exact And.right
  · intro hm
    refine ⟨mem_power_iff.mpr (fun p hp => mem_power_iff.mpr (fun s hs =>
      mem_power_iff.mpr (fun x hx => hm.1 p hp s hs x hx))), hm⟩

theorem definable_diagonal_pair : ℒₛₑₜ-function₁[V] (fun x : V => kpair x x) := by
  definability

noncomputable def identity (d : V) : V :=
  repl (fun x => kpair x x) definable_diagonal_pair d

theorem diagonal_at (d x y : V) : At E (identity d) x y ↔ x ∈ d ∧ y = x := by
  rw [at_iff_mem_kpair, identity, repl_spec]
  constructor
  · rintro ⟨z, hz, eq⟩
    have same := kpair_iff.mp eq
    exact ⟨same.1 ▸ hz, same.2.trans same.1.symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨_, hx, rfl⟩

theorem identity_mem_universe (d : V) : identity d ∈ assignments d := by
  apply (mem_universe d _).mpr
  constructor
  · intro p hp t ht x hx
    obtain ⟨a, ha, rfl⟩ := (repl_spec definable_diagonal_pair).mp hp
    have belongs := (kpair_is_pair a a t).mp ht
    rcases belongs.2 x hx with rfl | rfl <;> exact ha
  · intro x
    exact ⟨x.val, (diagonal_at d _ _).mpr ⟨x.property, rfl⟩,
      fun z hz => (diagonal_at d _ _).mp hz |>.2⟩

end I0451.Logic.SetAssignments
