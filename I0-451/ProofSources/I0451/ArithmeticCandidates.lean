module
public import I0451.ArithmeticScheduler

/-! The candidate enumeration starts at the checked literal startup
frame. Any internally finite witness that halts from a reached
candidate yields a witness for the blank-tape halting sentence. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime _root_.I0451.Decoder

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def initialModelTape : V := (ModelFrame.ofStandard (V := V) commandBoundary).tape

theorem initialModelTape_reaches : ReachesBoundary (initialModelTape : V) 3 0 := by
  let frame := ModelFrame.ofStandard (V := V) commandBoundary
  let registers := boundaryRegisters (3 : V) 0 0 1 0 0
  have castZero : ((0 : Nat) : V) = 0 := Nat.cast_zero
  have castOne : ((1 : Nat) : V) = 1 := Nat.cast_one
  have castThree : ((3 : Nat) : V) = 3 := Nat.cast_ofNat
  have fields : frame.regs = modelRegisters registers := by
    simp only [frame, ModelFrame.ofStandard, commandBoundary, modelRegisters, tapeRegistersWith,
      List.map_append, List.map_cons, List.map_nil, castZero, castOne, castThree]
    rfl
  have view : ModelRepresents frame 0 registers :=
    ⟨commandBoundary_model_permanent, boundarySearch_represents.address, fields⟩
  have ready : CommandReady registers := ⟨rfl, rfl, rfl⟩
  exact ReachesBoundary.of_frame (ModelReaches.refl literal frame.tape) view ready

theorem haltsDef_iff_initialModelTape :
    (haltsDef literal).val.Evalb (![] : Fin 0 → V) ↔ ModelRealizes (initialModelTape : V) .halt :=
  literal_halts_from_model_boundary

theorem model_candidate_available (candidate : V) (afterStart : (3 : V) ≤ candidate)
    (never : ¬ (haltsDef literal).val.Evalb (![] : Fin 0 → V)) :
    ReachesBoundary (initialModelTape : V) candidate 0 :=
  initialModelTape_reaches.candidate afterStart (never ∘ haltsDef_iff_initialModelTape.mpr)

/-- It suffices to prove a candidate's effect from every incoming proof
store. Its starting stack need not be recovered from the earlier run. -/
theorem literal_halts_of_model_candidate (candidate : V) (afterStart : (3 : V) ≤ candidate)
    (stops : ∀ (f : ModelFrame V) (s : Fin 9 → V),
      ModelRepresents f 0 s → CommandReady s →
      s nextProof = candidate → s proofList = 0 → ModelRealizes f.tape .halt) :
    (haltsDef literal).val.Evalb (![] : Fin 0 → V) := by
  by_contra never
  obtain ⟨f, s, reached, view, ready, index, queue⟩ :=
    (model_candidate_available candidate afterStart never).frame
  obtain ⟨elapsed, arrives⟩ := reached
  obtain ⟨rest, halted⟩ := stops f s view ready index (le_antisymm queue (by simp))
  exact never (haltsDef_iff_initialModelTape.mpr ⟨elapsed + rest, by
    rw [trace_add, arrives]
    exact halted⟩)

/-- Replay a model-definable command trace on the literal tape up to
its internally finite final instruction. -/
theorem model_halts_after_command_run {f : ModelFrame V} {states : V → Fin 9 → V}
    (initial : ModelRepresents f 0 (states 0))
    (defined : ∀ i, 𝚺ᴬ₁-Function₁[V] (fun j => states j i)) (limit : V)
    (ready : ∀ j ≤ limit, CommandReady (states j))
    (steps : ∀ j < limit, modelCommandStep (states j) = some (states (j + 1)))
    (stops : modelCommandStep (states limit) = none) : ModelRealizes f.tape .halt := by
  have edge : AtEdge ([] : List Bool) mainEdge := rfl
  have address : PackedAddress ([] : List Bool) := ⟨[], .empty _ _ _, rfl⟩
  have frameWidth : ([] : List Bool).length ≤ 94 := by decide
  have path : ∀ j ≤ limit, ReachesAt f.tape [] (states j) := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | zero =>
      intro _
      exact reachesAt_of_frame (ModelReaches.refl literal f.tape) initial frameWidth
    | succ j ih =>
      intro bounded
      have before := succ_le_iff_lt.mp bounded
      obtain ⟨atStart, reached, view⟩ := (ih (le_of_lt before)).frame address
      have ran := model_command_step (states j) (ready j (le_of_lt before))
      rw [steps j before] at ran
      have implements : ModelImplements atStart .normal [] (states (j + 1)) :=
        ModelEffect.run ran edge view
      obtain ⟨after, pc, movement, returned, newView⟩ := implements.advances (by decide)
      have rootAddress : pc = 0 := (Option.some.inj returned).symm
      exact reachesAt_of_frame (reached.trans movement) (rootAddress ▸ newView) frameWidth
    | hP =>
      have reachable := reachesAt_definable f.tape [] states defined
      definability
  obtain ⟨last, hit, view⟩ := (path limit (le_refl limit)).frame address
  have ran := model_command_step (states limit) (ready limit (le_refl _))
  rw [stops] at ran
  obtain ⟨output, halt⟩ := ran
  have actual : ModelImplements last .halt [] output := ModelEffect.run halt edge view
  have stopped : ModelRealizes last.tape .halt := actual.halts rfl
  obtain ⟨n, reaches⟩ := hit
  obtain ⟨m, finished⟩ := stopped
  exact ⟨n + m, by rw [trace_add, reaches]; exact finished⟩

end I0451.Arithmetization
