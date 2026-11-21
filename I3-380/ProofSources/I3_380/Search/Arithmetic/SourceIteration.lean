module
public import I3_380.Search.Arithmetic.ProgramRealization
public import I3_380.Search.Arithmetic.ProgramEquivalence
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PalomarI3380.Arithmetic (Chain)
open ArithmeticMachine.Reference (ReachesHalt)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Termination after an internal number of complete search trials. -/
def CodedTermination (s : M) : Prop :=
  ∃ n last final : M, Chain (main.Runs .normal) n s last ∧ main.Runs .halt last final

theorem CodedTermination.of_halt {s t : M} (stopped : main.Runs .halt s t) :
    CodedTermination s :=
  ⟨0,s,t,Chain.refl _ _,stopped⟩

theorem CodedTermination.prepend {s t : M} (first : main.Runs .normal s t)
    (stops : CodedTermination t) : CodedTermination s := by
  obtain ⟨n,last,final,trace,halt⟩ := stops
  exact ⟨1+n,last,final,(Chain.single first).trans trace,halt⟩

theorem codedTermination_definable : 𝚺ᴬ₁-Predicate (CodedTermination (M := M)) := by
  have trial := main.runs_definable (M := M) .normal
  have halt := main.runs_definable (M := M) .halt
  change 𝚺ᴬ₁.Definable (fun v : Fin 1 → M => CodedTermination (v 0))
  simp only [CodedTermination,Chain]
  definability

theorem CodedTermination.reachesHalt {origin s : M} {stem : List M}
    (nonempty : 0 < stem.length) (entry : ReachedAt origin stem [] s)
    (terminates : CodedTermination s) : ReachesHalt origin := by
  obtain ⟨n,last,final,trace,endRun⟩ := terminates
  have location : locate referenceProgram [] = some referenceProgram := rfl
  have lastReached : ReachedAt origin stem [] last :=
    trace.last_holds (ReachedAt origin stem []) (reachedAt_definable ..) entry
      (fun a b ready round => by
        have concrete := (model_reference_matches_source (M := M) .normal a b).mpr round
        simpa only [ReachedOut,show Flow.normal ≠ .halt by decide,↓reduceIte,destination,
          incrementPath,Engine.incrementReversed,List.reverse_nil] using
            concrete.realizes nonempty location ready)
  have halt := (model_reference_matches_source (M := M) .halt last final).mpr endRun
  simpa only [ReachedOut,↓reduceIte] using halt.realizes nonempty location lastReached

end PalomarI3380.Compiler.Source
