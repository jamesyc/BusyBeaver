module
public import I0451.ArithmeticCommandCoding

/-! Replay a coded command history of model-valued length on the
physical literal tape. Only the nine live register values are decoded. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem unpackBoundary_ready (code : V) : CommandReady (unpackBoundary code) :=
  ⟨rfl, rfl, rfl⟩

theorem pack_unpackBoundary {code : V} (live : code ≠ 0) :
    packBoundary (unpackBoundary code) = code := by
  have predecessor : 1 ≤ code := le_of_not_gt (fun lt => live (lt_one_iff_eq_zero.mp lt))
  simp [packBoundary, unpackBoundary, boundaryRegisters, nextProof, topWff, wffStack,
    parameterOne, parameterTwo, proofList, tsub_add_cancel_of_le predecessor]

structure CodedCommandRun (first : V) (history limit : V) : Prop where
  sequence : Seq history
  length : limit + 1 ≤ lh history
  start : znth history 0 = first
  live : ∀ j ≤ limit, znth history j ≠ 0
  steps : ∀ j < limit, boundaryCodeStep (znth history j) = znth history (j + 1)
  stop : boundaryCodeStep (znth history limit) = 0

theorem model_halts_of_coded_run {f : ModelFrame V} {s : Fin 9 → V}
    (view : ModelRepresents f 0 s) (initial : CommandReady s)
    {history limit : V} (ran : CodedCommandRun (packBoundary s) history limit) :
    ModelRealizes f.tape .halt := by
  let regs (j : V) := unpackBoundary (znth history j)
  have first : regs 0 = s := by
    change unpackBoundary (znth history 0) = s
    rw [ran.start, unpack_packBoundary initial]
  have defined (r : Fin 9) : 𝚺ᴬ₁-Function₁[V] (fun j => regs j r) := by
    have field := unpackBoundary_field_defined (V := V) r
    have src : 𝚺ᴬ₁-Function₁[V] (fun j => znth history j) := by definability
    exact Bounding.HierarchySymbol.DefinableFunction₁.comp (F := fun a => unpackBoundary a r) src
  have ready (j : V) : CommandReady (regs j) := unpackBoundary_ready _
  have calcStep (j : V) (before : j ≤ limit) :
      boundaryCodeStep (znth history j) = codeOfResult (modelCommandStep (regs j)) := by
    have live := ran.live j before
    exact ite_eq_right live
  have steps (j : V) (before : j < limit) :
      modelCommandStep (regs j) = some (regs (j + 1)) := by
    have positive := ran.live (j + 1) (succ_le_iff_lt.mpr before)
    have code := (calcStep j (le_of_lt before)).symm.trans (ran.steps j before)
    cases actual : modelCommandStep (regs j) with
    | none =>
      rw [actual] at code
      exact (positive code.symm).elim
    | some out =>
      have clean := (model_command_step_shape (ready j) actual).1
      rw [actual, codeOfResult_some] at code
      have result : regs (j + 1) = out := by
        change unpackBoundary (znth history (j + 1)) = out
        rw [← code, unpack_packBoundary clean]
      rw [result]
  have stop : modelCommandStep (regs limit) = none :=
    (codeOfResult_zero_iff _).mp ((calcStep _ (le_refl _)).symm.trans ran.stop)
  have atFirst : ModelRepresents f 0 (regs 0) := by rwa [first]
  exact model_halts_after_command_run atFirst defined limit (fun j _ => ready j) steps stop

theorem literal_halts_of_coded_candidate (candidate : V) (afterStart : (3 : V) ≤ candidate)
    (compiled : ∀ s : Fin 9 → V, CommandReady s → s nextProof = candidate → s proofList = 0 →
      ∃ history limit, CodedCommandRun (packBoundary s) history limit) :
    (haltsDef literal).val.Evalb (![] : Fin 0 → V) :=
  literal_halts_of_model_candidate candidate afterStart fun f s view ready number empty => by
    obtain ⟨history, limit, ran⟩ := compiled s ready number empty
    exact model_halts_of_coded_run view ready ran

end I0451.Arithmetization
