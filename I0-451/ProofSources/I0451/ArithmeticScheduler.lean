module
public import I0451.ArithmeticCommands

/-! Reachability of every candidate, up to an earlier halt, for
internally finite candidate indices in arbitrary arithmetic models. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime _root_.I0451.Decoder

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def boundaryTape (gap next top stack operand cache queue : V) : V :=
  modelFrame [] gap (modelRegisters (boundaryRegisters next top stack operand cache queue))

private theorem boundaryTape_defined :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v : Fin 7 → V =>
      boundaryTape (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := by
  unfold boundaryTape
  apply modelRegisterFrame_defined [] (fun v : Fin 7 → V => v 0)
    (fun v => boundaryRegisters (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
  · definability
  · intro i
    rcases index_cases i with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      dsimp [boundaryRegisters, nextProof, topWff, wffStack, axiomIndex,
        parameterOne, parameterTwo, scratchOne, scratchTwo, proofList] <;> definability

/-- A valid command boundary with the given candidate index and a queue
bounded by the supplied code. This predicate permits arithmetic induction. -/
def ReachesBoundary (start next maxQueue : V) : Prop :=
  ∃ gap top stack operand cache queue : V, (107 : V) ≤ gap ∧ queue ≤ maxQueue ∧
    ModelReaches literal start (boundaryTape gap next top stack operand cache queue)

private theorem reached_with_tape_defined (start : V) (tape : V → V → V → V)
    (td : 𝚺ᴬ₁-Function₃[V] tape) (next bound : V → V)
    (n : 𝚺ᴬ₁-Function₁[V] next) (b : 𝚺ᴬ₁-Function₁[V] bound) :
    𝚺ᴬ₁-Predicate[V] (fun j => ∃ gap values : V, (107 : V) ≤ gap ∧
      π₂ (π₂ (π₂ (π₂ values))) ≤ bound j ∧ ∃ t : V, trace literal t start = tape gap (next j) values) := by
  definability

private theorem reachesBoundary_family_defined (start : V) (next bound : V → V)
    (n : 𝚺ᴬ₁-Function₁[V] next) (b : 𝚺ᴬ₁-Function₁[V] bound) :
    𝚺ᴬ₁-Predicate[V] (fun j => ReachesBoundary start (next j) (bound j)) := by
  let tape (gap index values : V) :=
    boundaryTape gap index (π₁ values) (π₁ (π₂ values)) (π₁ (π₂ (π₂ values)))
      (π₁ (π₂ (π₂ (π₂ values)))) (π₂ (π₂ (π₂ (π₂ values))))
  have tapeDefined : 𝚺ᴬ₁-Function₃[V] tape := by
    let project : Fin 7 → (Fin 3 → V) → V :=
      ![fun v => v 0, fun v => v 1, fun v => π₁ (v 2), fun v => π₁ (π₂ (v 2)),
        fun v => π₁ (π₂ (π₂ (v 2))), fun v => π₁ (π₂ (π₂ (π₂ (v 2)))),
        fun v => π₂ (π₂ (π₂ (π₂ (v 2))))]
    change 𝚺ᴬ₁.DefinableFunction (V := V) (fun v : Fin 3 → V => tape (v 0) (v 1) (v 2))
    apply Bounding.HierarchySymbol.DefinableFunction.substitution (f := project) boundaryTape_defined
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      dsimp [project] <;> definability
  let Packed (j : V) := ∃ gap values : V, (107 : V) ≤ gap ∧
    π₂ (π₂ (π₂ (π₂ values))) ≤ bound j ∧ ∃ t : V, trace literal t start = tape gap (next j) values
  have defined : 𝚺ᴬ₁-Predicate[V] Packed := reached_with_tape_defined start tape tapeDefined next bound n b
  apply defined.of_iff
  intro j
  constructor
  · rintro ⟨gap, top, stack, operand, cache, queue, space, bounded, t, ran⟩
    refine ⟨gap, ⟪top, stack, operand, cache, queue⟫, space, ?_, t, ?_⟩
    · simpa using bounded
    · simpa [tape] using ran
  · rintro ⟨gap, values, space, bounded, t, ran⟩
    exact ⟨gap, _, _, _, _, _, space, bounded, t, ran⟩

private theorem boundary_address : PackedAddress ([] : List Bool) :=
  ⟨[], .empty _ _ _, rfl⟩

theorem ReachesBoundary.frame {start next maxQueue : V} (atBoundary : ReachesBoundary start next maxQueue) :
    ∃ f : ModelFrame V, ∃ s : Fin 9 → V, ModelReaches literal start f.tape ∧
      ModelRepresents f 0 s ∧ CommandReady s ∧ s nextProof = next ∧ s proofList ≤ maxQueue := by
  obtain ⟨gap, top, stack, operand, cache, queue, width, bound, reach⟩ := atBoundary
  let s := boundaryRegisters next top stack operand cache queue
  let f := makeModelFrame [] gap (modelRegisters s)
  have permanent : ModelPermanent f :=
    ⟨by simpa [f, makeModelFrame] using width, by simp [f, makeModelFrame],
      by simp [f, makeModelFrame, modelRegisters_length], boundary_address⟩
  exact ⟨f, s, by rwa [makeModelFrame_tape], ⟨permanent, rfl, rfl⟩,
    ⟨rfl, rfl, rfl⟩, rfl, bound⟩

theorem ReachesBoundary.of_frame {start : V} {f : ModelFrame V} {s : Fin 9 → V}
    (reach : ModelReaches literal start f.tape)
    (view : ModelRepresents f 0 s) (ready : CommandReady s) :
    ReachesBoundary start (s nextProof) (s proofList) := by
  have equal : f.tape = modelFrame [] f.slot (modelRegisters s) := by
    unfold ModelFrame.tape
    rw [view.registers]
    apply modelFrame_equal view.address
    simpa only [List.length_nil, Nat.cast_zero, add_zero] using sub_add_self_of_le view.good.wordFits
  refine ⟨f.slot, s topWff, s wffStack, s parameterOne, s parameterTwo, s proofList, view.good.space,
    le_refl _, ?_⟩
  unfold boundaryTape
  rwa [ready.boundaryRegisters, ← equal]

def ModelNeverHalts (start : V) : Prop := ¬ ModelRealizes start .halt

theorem ModelNeverHalts.advance {start : V} (never : ModelNeverHalts start)
    {f : ModelFrame V} {s : Fin 9 → V} (reach : ModelReaches literal start f.tape)
    (view : ModelRepresents f 0 s) (ready : CommandReady s) :
    ∃ g : ModelFrame V, ∃ t : Fin 9 → V,
      ModelReaches literal start g.tape ∧ ModelRepresents g 0 t ∧ modelCommandStep s = some t := by
  have ran := model_command_step s ready
  cases step : modelCommandStep s with
  | none =>
    rw [step] at ran
    obtain ⟨out, halt⟩ := ran
    have atRoot : AtEdge ([] : List Bool) mainEdge := rfl
    have actual : ModelImplements f .halt [] out := ModelEffect.run halt atRoot view
    have halted : ModelRealizes f.tape .halt := actual.halts rfl
    obtain ⟨n, arrival⟩ := reach
    obtain ⟨m, terminal⟩ := halted
    exact False.elim (never ⟨n + m, by rw [trace_add, arrival]; exact terminal⟩)
  | some out =>
    rw [step] at ran
    have atRoot : AtEdge ([] : List Bool) mainEdge := rfl
    have actual : ModelImplements f .normal [] out := ModelEffect.run ran atRoot view
    obtain ⟨g, address, movement, ret, newView⟩ := actual.advances (by decide)
    have rootAddress : address = 0 := (Option.some.inj ret).symm
    exact ⟨g, out, reach.trans movement, rootAddress ▸ newView, rfl⟩

private theorem ReachesBoundary.weaken {start next a b : V}
    (reach : ReachesBoundary start next a) (wider : a ≤ b) : ReachesBoundary start next b := by
  obtain ⟨gap, top, stack, operand, cache, queue, width, bound, visited⟩ := reach
  exact ⟨gap, top, stack, operand, cache, queue, width, bound.trans wider, visited⟩

/-- Unless the tape halts, a queued candidate is exhausted after
internally many commands, without changing the next candidate index. -/
theorem ReachesBoundary.drain {start next bound : V}
    (reach : ReachesBoundary start next bound) (never : ModelNeverHalts start) :
    ReachesBoundary start next 0 := by
  have each : ∀ j ≤ bound, ReachesBoundary start next (bound - j) := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | zero => simpa using fun _ : (0 : V) ≤ bound => reach
    | succ j ih =>
      intro fits
      have before := succ_le_iff_lt.mp fits
      have current := ih (le_of_lt before)
      obtain ⟨f, s, reached, view, ready, number, pending⟩ := current.frame
      by_cases empty : s proofList = 0
      · have root := ReachesBoundary.of_frame reached view ready
        rw [empty, number] at root
        exact root.weaken (by simp)
      · obtain ⟨g, t, moved, newView, step⟩ := never.advance reached view ready
        obtain ⟨clean, index, smaller⟩ := model_command_step_shape ready step
        rw [modelNextIndex, ite_eq_right empty, number] at index
        rw [modelPayload, ite_eq_right empty] at smaller
        have next := ReachesBoundary.of_frame moved newView clean
        rw [index] at next
        apply next.weaken (smaller.trans _)
        simpa only [Arithmetic.sub_sub] using (tsub_le_tsub_right pending 1)
    | hP =>
      have reachDefined := reachesBoundary_family_defined start (fun _ => next) (fun j => bound - j)
        (by definability) (by definability)
      definability
  simpa only [Arithmetic.sub_self] using each bound (le_refl _)

theorem ReachesBoundary.next {start k : V} (reach : ReachesBoundary start k 0)
    (never : ModelNeverHalts start) : ReachesBoundary start (k + 1) 0 := by
  obtain ⟨f, s, reached, view, ready, number, pending⟩ := reach.frame
  have empty : s proofList = 0 := le_antisymm pending (by simp)
  obtain ⟨g, t, moved, newView, step⟩ := never.advance reached view ready
  obtain ⟨clean, index, _⟩ := model_command_step_shape ready step
  rw [modelNextIndex, ite_eq_left empty, number] at index
  have next := ReachesBoundary.of_frame moved newView clean
  rw [index] at next
  exact next.drain never

/-- In a nonhalting literal trace every greater candidate occurs with
an empty queue, including candidate numbers outside the standard cut. -/
theorem ReachesBoundary.candidate {start first candidate : V}
    (reach : ReachesBoundary start first 0) (later : first ≤ candidate)
    (never : ModelNeverHalts start) : ReachesBoundary start candidate 0 := by
  have reaches : ∀ j : V, ReachesBoundary start (first + j) 0 := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | zero => simpa using reach
    | succ j ih => simpa only [Arithmetic.add_assoc] using ih.next never
    | hP =>
      exact reachesBoundary_family_defined start (fun j => first + j) (fun _ => 0)
        (by definability) (by definability)
  simpa only [add_tsub_cancel_of_le later] using reaches (candidate - first)

end I0451.Arithmetization
