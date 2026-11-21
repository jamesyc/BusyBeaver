module
public import I0451.Logic.SetAssignments

/-! Construct the least family of relative truth sets inside a ZF model.
The construction uses Separation on the power set of the assignment
universe. Each operation has a unique trace on that universe. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

def agreeDef : SetTheorySemisentence 3 :=
  “i g h. ∀ p ∈ g, p ∉ h → ∀ a ∈ p, i ∈ a”

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
@[simp] theorem eval_agreeDef (i g h : V) : agreeDef.Evalb ![i,g,h] ↔ Agree E i g h := by
  simp [agreeDef, Agree]

def AtomTrace (g i k : V) : Prop := ∀ x y, At E g i x → At E g k y → x ∈ y

def StepTrace (g U i R S : V) : Prop :=
  ∃ u ∈ U, (u ∈ R → u ∈ S) ∧ Agree E i g u

def atomTraceDef : SetTheorySemisentence 3 :=
  “g i k. ∀ x y, !atDef g i x → !atDef g k y → x ∈ y”

def stepTraceDef : SetTheorySemisentence 5 :=
  “g U i R S. ∃ u ∈ U, (u ∈ R → u ∈ S) ∧ !agreeDef i g u”

@[simp] theorem eval_atomTraceDef (g i k : V) :
    atomTraceDef.Evalb ![g,i,k] ↔ AtomTrace g i k := by
  simp [atomTraceDef, AtomTrace]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
@[simp] theorem eval_stepTraceDef (g U i R S : V) :
    stepTraceDef.Evalb ![g,U,i,R,S] ↔ StepTrace g U i R S := by
  simp [stepTraceDef, StepTrace]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem predicateWith {n : Nat} (formula : SetTheorySemisentence (n + 1)) (parameters : Fin n → V) :
    ℒₛₑₜ-predicate (fun x : V => formula.Evalb (x :> parameters)) := by
  let terms : Fin (n + 1) → SetTheorySemiterm V 1 := #0 :> fun i => &(parameters i)
  refine ⟨(Rew.embSubsts terms) ▹ formula, fun v => ?_⟩
  rw [Semiformula.eval_embSubsts]
  have args : (Semiterm.val (L := ℒₛₑₜ) v id ∘ terms) = (v 0 :> parameters) := by
    funext j
    cases j using Fin.cases <;> rfl
  rw [args]

noncomputable def atomicSet (U i k : V) : V :=
  sep U (AtomTrace · i k) (by
    have h := predicateWith atomTraceDef ![i,k]
    exact h.of_iff fun g => (eval_atomTraceDef g i k).symm)

noncomputable def stepSet (U i R S : V) : V :=
  sep U (StepTrace · U i R S) (by
    have h := predicateWith stepTraceDef ![U,i,R,S]
    exact h.of_iff fun g => (eval_stepTraceDef g U i R S).symm)

theorem mem_atomicSet (U i k g : V) : g ∈ atomicSet U i k ↔ g ∈ U ∧ AtomTrace g i k :=
  mem_sep_iff

theorem mem_stepSet (U i R S g : V) : g ∈ stepSet U i R S ↔ g ∈ U ∧ StepTrace g U i R S :=
  mem_sep_iff

structure ClosedFamily (d U C : V) : Prop where
  subset : ∀ R ∈ C, R ⊆ U
  atom : ∀ i k, i ∈ d → k ∈ d → atomicSet U i k ∈ C
  step : ∀ i R S, i ∈ d → R ∈ C → S ∈ C → stepSet U i R S ∈ C

def closedFamilyDef : SetTheorySemisentence 3 :=
  “C d U. (∀ R ∈ C, R ⊆ U) ∧
    (∀ i ∈ d, ∀ k ∈ d, ∃ R ∈ C, ∀ g, g ∈ R ↔ g ∈ U ∧ !atomTraceDef g i k) ∧
    (∀ i ∈ d, ∀ R ∈ C, ∀ S ∈ C, ∃ W ∈ C, ∀ g, g ∈ W ↔ g ∈ U ∧ !stepTraceDef g U i R S)”

theorem eval_closedFamilyDef (d U C : V) :
    closedFamilyDef.Evalb ![C,d,U] ↔ ClosedFamily d U C := by
  have atomEval (g i k : V) :
      atomTraceDef.Eval (g :> i :> fun _ : Fin 1 => k) Empty.elim ↔ AtomTrace g i k := by
    simpa only [Matrix.vec_single_eq_const] using eval_atomTraceDef g i k
  have stepEval (g U i R S : V) :
      stepTraceDef.Eval (g :> U :> i :> R :> fun _ : Fin 1 => S) Empty.elim ↔ StepTrace g U i R S := by
    simpa only [Matrix.vec_single_eq_const] using eval_stepTraceDef g U i R S
  simp [closedFamilyDef, Matrix.comp_vecCons', Function.comp_def, atomEval, stepEval]
  change ((∀ R ∈ C, R ⊆ U) ∧
    (∀ i ∈ d, ∀ k ∈ d, ∃ R ∈ C, ∀ g, g ∈ R ↔ g ∈ U ∧ AtomTrace g i k) ∧
    (∀ i ∈ d, ∀ R ∈ C, ∀ S ∈ C, ∃ W ∈ C, ∀ g, g ∈ W ↔ g ∈ U ∧ StepTrace g U i R S)) ↔ _
  constructor
  · rintro ⟨inside, atoms, steps⟩
    refine ⟨inside, ?_, ?_⟩
    · intro i k hi hk
      obtain ⟨R, mem, exactTrace⟩ := atoms i hi k hk
      have same : R = atomicSet U i k := mem_ext_iff.mpr fun g =>
        (exactTrace g).trans (mem_atomicSet U i k g).symm
      exact same ▸ mem
    · intro i R S hi hr hs
      obtain ⟨W, mem, exactTrace⟩ := steps i hi R hr S hs
      have same : W = stepSet U i R S := mem_ext_iff.mpr fun g =>
        (exactTrace g).trans (mem_stepSet U i R S g).symm
      exact same ▸ mem
  · intro family
    refine ⟨family.subset, ?_, ?_⟩
    · exact fun i hi k hk => ⟨_, family.atom i k hi hk, mem_atomicSet U i k⟩
    · exact fun i hi R hr S hs => ⟨_, family.step i R S hi hr hs, mem_stepSet U i R S⟩

def generatedDef : SetTheorySemisentence 3 := “R d U. ∀ C, !closedFamilyDef C d U → R ∈ C”

theorem eval_generatedDef (R d U : V) :
    generatedDef.Evalb ![R,d,U] ↔ ∀ C, ClosedFamily d U C → R ∈ C := by
  simp [generatedDef, eval_closedFamilyDef]

noncomputable def generated (d U : V) : V :=
  sep (℘ U) (fun R => ∀ C, ClosedFamily d U C → R ∈ C) (by
    have h := predicateWith generatedDef ![d,U]
    exact h.of_iff fun R => (eval_generatedDef R d U).symm)

theorem mem_generated (R d U : V) :
    R ∈ generated d U ↔ R ⊆ U ∧ ∀ C, ClosedFamily d U C → R ∈ C := by
  rw [generated, mem_sep_iff, mem_power_iff]

theorem generated_closed (d U : V) : ClosedFamily d U (generated d U) where
  subset := fun R h => ((mem_generated R d U).mp h).1
  atom := by
    intro i k hi hk
    exact (mem_generated _ d U).mpr
      ⟨fun g h => ((mem_atomicSet U i k g).mp h).1, fun C c => c.atom i k hi hk⟩
  step := by
    intro i R S hi hr hs
    exact (mem_generated _ d U).mpr
      ⟨fun g h => ((mem_stepSet U i R S g).mp h).1, fun C c =>
        c.step i R S hi (((mem_generated R d U).mp hr).2 C c) (((mem_generated S d U).mp hs).2 C c)⟩

theorem generated_truthSets (d : V) :
    TruthSets E d (assignments d) (generated d (assignments d)) where
  codes := mem_universe d
  atom := by
    intro i k
    have family := generated_closed d (assignments d)
    exact ⟨_, family.atom i.val k.val i.property k.property, fun g hg =>
      (mem_atomicSet _ i.val k.val g).trans (and_iff_right hg)⟩
  close := by
    intro i R S hr hs
    have family := generated_closed d (assignments d)
    exact ⟨_, family.step i.val R S i.property hr hs, fun g hg =>
      (mem_stepSet _ i.val R S g).trans (and_iff_right hg)⟩

end I0451.Logic.SetAssignments
