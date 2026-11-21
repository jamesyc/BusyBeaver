module
public import I0451.Logic.TruthFamily

/-! The least closed family is reached in internally finite stages.
The stage number belongs to the model's omega, so the result applies
also in nonstandard models of ZF. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def Growth (R d U C : V) : Prop :=
  R ∈ C ∨ (∃ i ∈ d, ∃ k ∈ d, R = atomicSet U i k) ∨
    (∃ i ∈ d, ∃ P ∈ C, ∃ Q ∈ C, R = stepSet U i P Q)

def growthDef : SetTheorySemisentence 4 :=
  “R d U C. R ∈ C ∨
    (∃ i ∈ d, ∃ k ∈ d, ∀ g, g ∈ R ↔ g ∈ U ∧ !atomTraceDef g i k) ∨
    (∃ i ∈ d, ∃ P ∈ C, ∃ Q ∈ C, ∀ g, g ∈ R ↔ g ∈ U ∧ !stepTraceDef g U i P Q)”

theorem eval_growthDef (R d U C : V) : growthDef.Evalb ![R,d,U,C] ↔ Growth R d U C := by
  have atomEval (g i k : V) :
      atomTraceDef.Eval (g :> i :> fun _ : Fin 1 => k) Empty.elim ↔ AtomTrace g i k := by
    simpa only [Matrix.vec_single_eq_const] using eval_atomTraceDef g i k
  have stepEval (g U i P Q : V) :
      stepTraceDef.Eval (g :> U :> i :> P :> fun _ : Fin 1 => Q) Empty.elim ↔ StepTrace g U i P Q := by
    simpa only [Matrix.vec_single_eq_const] using eval_stepTraceDef g U i P Q
  simp [growthDef, Matrix.comp_vecCons', Function.comp_def, atomEval, stepEval]
  simp only [Growth, mem_ext_iff (x := R) (y := atomicSet _ _ _),
    mem_ext_iff (x := R) (y := stepSet _ _ _ _), mem_atomicSet, mem_stepSet]

noncomputable def grow (d U C : V) : V :=
  sep (℘ U) (fun R => Growth R d U C) (by
    have h := predicateWith growthDef ![d,U,C]
    exact h.of_iff fun R => (eval_growthDef R d U C).symm)

theorem mem_grow (d U C R : V) : R ∈ grow d U C ↔ R ⊆ U ∧ Growth R d U C := by
  rw [grow, mem_sep_iff, mem_power_iff]

theorem grow_retains {d U C : V} (subsets : ∀ R ∈ C, R ⊆ U) : C ⊆ grow d U C :=
  fun R h => (mem_grow d U C R).mpr ⟨subsets R h, .inl h⟩

theorem atom_mem_grow {d U C i k : V} (hi : i ∈ d) (hk : k ∈ d) :
    atomicSet U i k ∈ grow d U C :=
  (mem_grow _ _ _ _).mpr ⟨fun g h => ((mem_atomicSet U i k g).mp h).1, .inr (.inl ⟨i, hi, k, hk, rfl⟩)⟩

theorem step_mem_grow {d U C i P Q : V} (hi : i ∈ d) (hp : P ∈ C) (hq : Q ∈ C) :
    stepSet U i P Q ∈ grow d U C :=
  (mem_grow _ _ _ _).mpr ⟨fun g h => ((mem_stepSet U i P Q g).mp h).1, .inr (.inr ⟨i, hi, P, hp, Q, hq, rfl⟩)⟩

theorem grow_subset_closed {d U C K : V} (below : C ⊆ K) (closed : ClosedFamily d U K) :
    grow d U C ⊆ K := by
  intro R h
  rcases ((mem_grow _ _ _ _).mp h).2 with old | ⟨i, hi, k, hk, rfl⟩ | ⟨i, hi, P, hp, Q, hq, rfl⟩
  · exact below R old
  · exact closed.atom i k hi hk
  · exact closed.step i P Q hi (below P hp) (below Q hq)

def growthBlueprint : NaturalNumberRec.Blueprint 2 where
  zero := “W d U. ∀ x, x ∉ W”
  succ := “W C n d U. ∀ R, R ∈ W ↔ R ⊆ U ∧ !growthDef R d U C”

noncomputable def growthIteration : NaturalNumberRec.Construction V growthBlueprint where
  zero := fun _ => ∅
  succ := fun env _ C => grow (env 0) (env 1) C
  zero_defined := ⟨fun v => by
    simpa [growthBlueprint, isEmpty, FFL.FirstOrder.SetTheory.IsEmpty,
      Matrix.comp_vecCons', Function.comp_def] using (isEmpty_iff_eq_empty (x := v 0))⟩
  succ_defined := ⟨fun v => by
    have eval (R : V) :
        growthDef.Eval (R :> v 3 :> v 4 :> fun _ : Fin 1 => v 1) Empty.elim ↔
          Growth R (v 3) (v 4) (v 1) := by
      simpa only [Matrix.vec_single_eq_const] using eval_growthDef R (v 3) (v 4) (v 1)
    simp [growthBlueprint, Matrix.comp_vecCons', Function.comp_def, eval]
    simp only [← mem_grow, ← mem_ext_iff]⟩

noncomputable def truthStage (n d U : V) : V := growthIteration.result ![d,U] n

theorem truthStage_zero (d U : V) : truthStage 0 d U = ∅ :=
  growthIteration.result_zero ![d,U]

theorem truthStage_succ {n : V} (hn : n ∈ (ω : V)) (d U : V) :
    truthStage (succ n) d U = grow d U (truthStage n d U) :=
  growthIteration.result_succ ![d,U] hn

theorem truthStage_defined (d U : V) :
    ℒₛₑₜ-function₁[V] (fun k => truthStage k d U) := by
  let params : Fin 3 → (Fin 1 → V) → V := ![fun v => v 0, fun _ => d, fun _ => U]
  have defined := (growthIteration (V := V)).result_definable
  have arguments (i : Fin 3) : Language.DefinableFunction ℒₛₑₜ (params i) := by
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> dsimp [params] <;> definability
  have joined := Language.DefinableFunction.substitution (f := params) defined arguments
  have parameters (v : Fin 1 → V) : (fun i : Fin 2 => params i.succ v) = ![d,U] := by
    funext i
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl <;> rfl
  have clock (v : Fin 1 → V) : params 0 v = v 0 := rfl
  simpa only [parameters, clock, truthStage] using joined

attribute [local irreducible] truthStage

theorem truthStage_subset_closed {n d U C : V} (hn : n ∈ (ω : V)) (closed : ClosedFamily d U C) :
    truthStage n d U ⊆ C := by
  apply naturalNumber_induction (fun k => truthStage k d U ⊆ C) _ _ _ n hn
  · have stage := truthStage_defined d U
    definability
  · rw [truthStage_zero]
    simp [subset_def]
  · intro k hk ih
    rw [truthStage_succ hk]
    exact grow_subset_closed ih closed

theorem truthStage_subsets {n d U R : V} (hn : n ∈ (ω : V)) (hR : R ∈ truthStage n d U) :
    R ⊆ U := by
  have closed := generated_closed d U
  exact closed.subset R (truthStage_subset_closed hn closed R hR)

private theorem stagesOrdered_defined (F : V → V) (defined : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-predicate[V] (fun n => ∀ j ∈ n, F j ⊆ F n) := by
  definability

theorem truthStage_mono {n m d U : V} (hm : m ∈ (ω : V)) (before : n ∈ m) :
    truthStage n d U ⊆ truthStage m d U := by
  have each : ∀ k ∈ (ω : V), ∀ j ∈ k, truthStage j d U ⊆ truthStage k d U := by
    apply naturalNumber_induction (fun k => ∀ j ∈ k, truthStage j d U ⊆ truthStage k d U)
    · exact stagesOrdered_defined _ (truthStage_defined d U)
    · intro j impossible
      simp [zero_def] at impossible
    · intro k hk ih j hj
      rw [truthStage_succ hk]
      have next := grow_retains (d := d) (U := U) (C := truthStage k d U)
        (fun R hR => truthStage_subsets hk hR)
      rcases mem_succ_iff.mp hj with rfl | earlier
      · exact next
      · exact subset_trans (ih j earlier) next
  exact each m hm n before

theorem stageMembership_defined (F : V → V) (defined : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-predicate[V] (fun R => ∃ n ∈ (ω : V), R ∈ F n) := by
  definability

noncomputable def finiteStages (d U : V) : V :=
  sep (℘ U) (fun R => ∃ n ∈ (ω : V), R ∈ truthStage n d U)
    (stageMembership_defined _ (truthStage_defined d U))

theorem mem_finiteStages (d U R : V) :
    R ∈ finiteStages d U ↔ ∃ n ∈ (ω : V), R ∈ truthStage n d U := by
  rw [finiteStages, mem_sep_iff, mem_power_iff]
  exact ⟨fun h => h.2, fun ⟨n, hn, hR⟩ => ⟨truthStage_subsets hn hR, n, hn, hR⟩⟩

theorem finiteStages_closed (d U : V) : ClosedFamily d U (finiteStages d U) where
  subset := by
    intro R hR
    obtain ⟨n, hn, atStage⟩ := (mem_finiteStages d U R).mp hR
    exact truthStage_subsets hn atStage
  atom := by
    intro i k hi hk
    apply (mem_finiteStages d U _).mpr
    refine ⟨succ 0, ω_succ_closed zero_mem_ω, ?_⟩
    rw [truthStage_succ zero_mem_ω]
    exact atom_mem_grow hi hk
  step := by
    intro i P Q hi hp hq
    obtain ⟨n, hn, first⟩ := (mem_finiteStages d U P).mp hp
    obtain ⟨m, hm, second⟩ := (mem_finiteStages d U Q).mp hq
    let a : Ordinal V := (IsOrdinal.of_mem hn).toOrdinal
    let b : Ordinal V := (IsOrdinal.of_mem hm).toOrdinal
    rcases lt_trichotomy a b with earlier | same | later
    · apply (mem_finiteStages d U _).mpr
      refine ⟨succ m, ω_succ_closed hm, ?_⟩
      rw [truthStage_succ hm]
      exact step_mem_grow hi (truthStage_mono hm earlier P first) second
    · have index : n = m := congrArg Ordinal.val same
      subst m
      apply (mem_finiteStages d U _).mpr
      refine ⟨succ n, ω_succ_closed hn, ?_⟩
      rw [truthStage_succ hn]
      exact step_mem_grow hi first second
    · apply (mem_finiteStages d U _).mpr
      refine ⟨succ n, ω_succ_closed hn, ?_⟩
      rw [truthStage_succ hn]
      exact step_mem_grow hi first (truthStage_mono hn later Q second)

/-- The family in the exact emitted formula has no members beyond those
produced by an internally finite computation from the atomic relations. -/
theorem generated_eq_finiteStages (d U : V) : generated d U = finiteStages d U := by
  apply mem_ext_iff.mpr
  intro R
  constructor
  · intro h
    exact ((mem_generated R d U).mp h).2 _ (finiteStages_closed d U)
  · intro h
    obtain ⟨n, hn, stage⟩ := (mem_finiteStages d U R).mp h
    exact truthStage_subset_closed hn (generated_closed d U) R stage

end I0451.Logic.SetAssignments
