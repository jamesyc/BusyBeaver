module
public import I0451.ArithmeticPermanent

/-! The initial frame for arithmetic instruction proofs and an interface
for chaining instructions along internally finite register paths. -/

@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ModelFrame.ofStandard (f : RegisterFrame) : ModelFrame V :=
  ⟨f.word, (f.slot : V), f.regs.map (fun n : Nat => (↑n : V))⟩

theorem ModelFrame.ofStandard_tape (f : RegisterFrame) (fits : f.word.length ≤ f.slot) :
    (ModelFrame.ofStandard (V := V) f).tape = (encodeConfig f.tape : V) := by
  unfold ModelFrame.ofStandard ModelFrame.tape RegisterFrame.tape
  have exactGap : (f.slot : V) - (f.word.length : V) =
      ((f.slot - f.word.length : Nat) : V) := by
    have asSum : (f.slot : V) = ((f.slot - f.word.length : Nat) : V) + (f.word.length : V) := by
      rw [← Nat.cast_add, Nat.sub_add_cancel fits]
    exact (tsub_eq_iff_eq_add_of_le (Nat.cast_le.mpr fits)).mpr asSum
  rw [exactGap, modelFrame_cast]

theorem ModelFrame.ofStandard_permanent (f : RegisterFrame) (good : Permanent f) :
    ModelPermanent (ModelFrame.ofStandard (V := V) f) := by
  refine ⟨?_, Nat.cast_le.mpr good.wordFits, ?_, good.address⟩
  · simpa only [ModelFrame.ofStandard, Nat.cast_ofNat] using (Nat.cast_le (α := V)).mpr good.space
  · simpa only [ModelFrame.ofStandard, List.length_map] using good.enoughRegisters

/-- The compiled proof search starts from a permanent arithmetic frame. -/
theorem commandBoundary_model_permanent :
    ModelPermanent (ModelFrame.ofStandard (V := V) commandBoundary) :=
  ModelFrame.ofStandard_permanent commandBoundary commandBoundary_permanent

theorem literal_halts_from_model_boundary :
    (haltsDef literal).val.Evalb (![] : Fin 0 → V) ↔
      ∃ n : V, Terminal literal
        (trace literal n (ModelFrame.ofStandard (V := V) commandBoundary).tape) := by
  rw [ModelFrame.ofStandard_tape commandBoundary commandBoundary_permanent.wordFits]
  exact literal_halts_from_boundary

theorem model_instruction_progress {f : ModelFrame V} (good : ModelPermanent f) :
    modelMacroStep f = ModelMacroResult.halt ∧ ModelRealizes f.tape .halt ∨
      ∃ next, modelMacroStep f = .next next ∧ ModelPermanent next ∧ ModelReaches literal f.tape next.tape := by
  have sound := modelMacroStep_sound f
  have safe := modelMacroStep_preserves good
  cases step : modelMacroStep f with
  | invalid =>
    rw [step] at safe
    exact False.elim safe
  | halt => exact Or.inl ⟨rfl, by simpa only [step] using sound⟩
  | next next => exact Or.inr ⟨next, rfl, by simpa only [step, ModelPreserves] using safe,
      by simpa only [step, ModelRealizes] using sound⟩

private theorem modelPack_function {k : Nat} (word : List Bool) (tail : (Fin k → V) → V)
    (defined : 𝚺ᴬ₁.DefinableFunction (V := V) tail) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun n => modelPack word (tail n)) := by
  induction word with
  | nil => exact defined
  | cons b rest ih =>
    simp only [modelPack_cons, modelPush]
    definability

private theorem modelBlocks_function {k : Nat} (regs : List ((Fin k → V) → V)) (tail : (Fin k → V) → V)
    (defined : ∀ f ∈ regs, 𝚺ᴬ₁.DefinableFunction (V := V) f) (tailDefined : 𝚺ᴬ₁.DefinableFunction (V := V) tail) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun n => modelBlocks (regs.map (fun f => f n)) (tail n)) := by
  induction regs with
  | nil => exact tailDefined
  | cons f rest ih =>
    have first := defined f (by simp)
    have following := ih (fun g mem => defined g (List.mem_cons_of_mem _ mem))
    simp only [List.map_cons, modelBlocks, modelPush]
    definability

/-- The encoding of a fixed instruction address, with a varying gap and
register contents, has a first-order graph suitable for arithmetic induction. -/
theorem modelFrame_family_definable {k : Nat} (word : List Bool) (gap : (Fin k → V) → V)
    (regs : List ((Fin k → V) → V))
    (gapDefined : 𝚺ᴬ₁.DefinableFunction (V := V) gap) (regDefined : ∀ f ∈ regs, 𝚺ᴬ₁.DefinableFunction (V := V) f) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun n => modelFrame word (gap n) (regs.map (fun f => f n))) := by
  have zeroDefined : 𝚺ᴬ₁.DefinableFunction (V := V) (fun _ : Fin k → V => (0 : V)) := by definability
  have blocks := modelBlocks_function regs (fun _ => 0) regDefined zeroDefined
  let tapeTail (n : Fin k → V) := modelRepeat false (gap n) (modelBlocks (regs.map (fun f => f n)) 0)
  have tailDefined : 𝚺ᴬ₁.DefinableFunction (V := V) tapeTail := by
    dsimp only [tapeTail]
    definability
  have packed := modelPack_function word tapeTail tailDefined
  change 𝚺ᴬ₁.DefinableFunction (V := V) (fun n => modelConfig root 1 (modelPack word (tapeTail n)))
  unfold modelConfig
  definability

theorem modelFrame_path_definable (word : List Bool) (gap : V → V) (regs : List (V → V))
    (gapDefined : 𝚺ᴬ₁-Function₁[V] gap) (regDefined : ∀ f ∈ regs, 𝚺ᴬ₁-Function₁[V] f) :
    𝚺ᴬ₁-Function₁[V] (fun n => modelFrame word (gap n) (regs.map (fun f => f n))) := by
  let lifted := regs.map (fun f => fun v : Fin 1 → V => f (v 0))
  have fields : ∀ f ∈ lifted, 𝚺ᴬ₁.DefinableFunction (V := V) f := by
    intro f contains
    obtain ⟨g, belongs, rfl⟩ := List.mem_map.mp contains
    exact regDefined g belongs
  simpa only [lifted, List.map_map, Function.comp_def] using
    modelFrame_family_definable word (fun v : Fin 1 → V => gap (v 0)) lifted gapDefined fields

end I0451.Arithmetization
