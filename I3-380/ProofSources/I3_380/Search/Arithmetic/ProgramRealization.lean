module
public import I3_380.Search.Arithmetic.FrameReach
public import I3_380.Search.Arithmetic.ProgramRuns
@[expose] public section

namespace PalomarI3380.Compiler

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.Reference (ReachesHalt)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem reachedAt_path {origin code : M} {stem : List M} {p q : List Bool}
    (same : trimPC p = trimPC q) (after : ReachedAt origin stem p code) :
    ReachedAt origin stem q code := by
  simpa only [ReachedAt,frameFromCode,same] using after

def ReachedOut (origin : M) (stem : List M) (path : List Bool) (out : Flow) (code : M) : Prop :=
  if out = .halt then ReachesHalt origin else ReachedAt origin stem (destination path out) code

/-- A model-finite structured execution is realized by the reference
clock. At a loop boundary, arithmetic induction transports reachability
of the same static path through the coded register stores. -/
theorem Program.Runs.realizes {p : Program} {origin start finish : M} {stem : List M}
    (nonempty : 0 < stem.length) {out : Flow} (run : p.Runs out start finish)
    {path : List Bool} (location : locate referenceProgram path = some p)
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

end PalomarI3380.Compiler
