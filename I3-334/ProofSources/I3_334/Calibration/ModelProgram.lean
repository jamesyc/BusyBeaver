module
public import I3_334.Calibration.ModelFrame
public import I3_334.Simulation.CompiledProgram
public import I3_334Support.Search.Arithmetic.ProgramEquivalence
@[expose] public section

namespace PalomarI3334.ModelFrame

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Arithmetic (Chain)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem reachedAt_path {origin code : M} {stem : List M} {p q : List Bool}
    (same : trimPC p = trimPC q) (after : ReachedAt origin stem p code) :
    ReachedAt origin stem q code := by
  simpa only [ReachedAt,frameOf,same] using after

def ReachedOut (origin : M) (stem : List M) (path : List Bool) (out : Flow) (code : M) : Prop :=
  if out = .halt then ReachesHalt origin else ReachedAt origin stem (destination path out) code

/-- A model-finite structured execution is realized by the reference
clock. At a loop boundary, arithmetic induction transports reachability
of the same static path through the coded register stores. -/
theorem program_realizes {p : Program} {origin start finish : M} {stem : List M}
    (nonempty : 0 < stem.length) {out : Flow} (run : p.Runs out start finish)
    {path : List Bool} (location : locate PalomarI3334.referenceProgram path = some p)
    (reached : ReachedAt origin stem path start) :
    ReachedOut origin stem path out finish := by
  induction p generalizing path out start finish with
  | op instruction =>
    have endLength := run.store_length reached.1
    change instruction.Runs out start finish at run
    have step := step_at_op location (Store.ofCode start)
    rw [run.effect_matches] at step
    by_cases stop : out = .halt
    · simpa only [ReachedOut,stop,↓reduceIte] using
        halt_reachedAt nonempty reached (by simpa only [stop,↓reduceIte] using step)
    · simp only [ReachedOut,stop,↓reduceIte]
      exact advance_reachedAt nonempty reached
        (by simpa only [stop,↓reduceIte] using step) endLength
  | seq p q left right =>
    have leftLocation := locate_left location
    have rightLocation := locate_right location
    have intoLeft {code : M} (ready : ReachedAt origin stem path code) :
        ReachedAt origin stem (path ++ [false]) code :=
      reachedAt_path (trimPC_append_zero path).symm ready
    have intoRight {a b : M} (first : p.Runs .normal a b)
        (ready : ReachedAt origin stem path a) :
        ReachedAt origin stem (path ++ [true]) b := by
      have step := left first leftLocation (intoLeft ready)
      have target : ReachedAt origin stem (destination (path ++ [false]) .normal) b := by
        simpa only [ReachedOut,show Flow.normal ≠ .halt by decide,↓reduceIte] using step
      exact reachedAt_path (by rw [destination,increment_left]) target
    obtain ⟨steps,last,trace,exit⟩ := run
    have carries : ReachedAt origin stem path last := trace.last_holds
      (ReachedAt origin stem path) (reachedAt_definable ..) reached
      (fun a b ready ⟨mid,first,again⟩ => by
        have next := right again rightLocation (intoRight first ready)
        simpa only [ReachedOut,show Flow.repeatAt 0 ≠ .halt by decide,↓reduceIte,destination_right_loop]
          using next)
    rcases exit with leftExit | ⟨mid,first,second⟩
    · have result := left leftExit leftLocation (intoLeft carries)
      by_cases stop : out = .halt
      · subst out
        simpa [ReachedOut,Flow.leftInput] using result
      · have continues : out.leftInput ≠ .halt := by
          cases out <;> simp_all [Flow.leftInput]
        simp only [ReachedOut,stop,continues,↓reduceIte] at result ⊢
        exact reachedAt_path (destination_left_exit _ (Flow.leftInput_exit out)) result
    · have result := right second rightLocation (intoRight first carries)
      by_cases stop : out = .halt
      · subst out
        simpa [ReachedOut,Flow.rightInput] using result
      · have continues : out.rightInput ≠ .halt := by
          cases out <;> simp_all [Flow.rightInput]
        simp only [ReachedOut,stop,continues,↓reduceIte] at result ⊢
        exact reachedAt_path (destination_right_exit _ (Flow.rightInput_exit out) stop) result


end PalomarI3334.ModelFrame

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Arithmetic (Chain)
open ModelFrame
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem model_reference_matches_source : CodeEquivalent M PalomarI3334.referenceProgram main :=
  equivalent_under_laws (codedNormalizationLaws M) reference_normalized_eq

def CodedTermination (s : M) : Prop :=
  ∃ n last final : M, Chain (main.Runs .normal) n s last ∧ main.Runs .halt last final

theorem CodedTermination.of_halt {s t : M} (stopped : main.Runs .halt s t) :
    CodedTermination s :=
  ⟨0,s,t,Chain.refl _ _,stopped⟩

theorem CodedTermination.prepend {s t : M} (first : main.Runs .normal s t)
    (stops : CodedTermination t) : CodedTermination s := by
  obtain ⟨n,last,final,trace,done⟩ := stops
  exact ⟨1+n,last,final,(Chain.single first).trans trace,done⟩

theorem codedTermination_definable : 𝚺ᴬ₁-Predicate (CodedTermination (M := M)) := by
  have trial := main.runs_definable (M := M) .normal
  have done := main.runs_definable (M := M) .halt
  change 𝚺ᴬ₁.Definable (fun v : Fin 1 → M => CodedTermination (v 0))
  simp only [CodedTermination,Chain]
  definability

/-- A model-finite sequence of exact trials is a literal halting trace.
The induction is on an arithmetically coded chain. -/
theorem CodedTermination.reachesHalt {origin s : M} {stem : List M}
    (nonempty : 0 < stem.length) (entry : ModelFrame.ReachedAt origin stem [] s)
    (terminates : CodedTermination s) : ReachesHalt origin := by
  obtain ⟨n,last,final,trace,endRun⟩ := terminates
  have location : locate PalomarI3334.referenceProgram [] = some PalomarI3334.referenceProgram := rfl
  have lastReached : ModelFrame.ReachedAt origin stem [] last :=
    trace.last_holds (ModelFrame.ReachedAt origin stem []) (ModelFrame.reachedAt_definable ..) entry
      (fun a b ready round => by
        have concrete := (model_reference_matches_source (M := M) .normal a b).mpr round
        simpa only [ReachedOut,show Flow.normal ≠ .halt by decide,↓reduceIte,destination,
          incrementPath,Engine.incrementReversed,List.reverse_nil] using
            program_realizes nonempty concrete location ready)
  have done := (model_reference_matches_source (M := M) .halt last final).mpr endRun
  simpa only [ReachedOut,↓reduceIte] using program_realizes nonempty done location lastReached

end PalomarI3334.SearchProgram
