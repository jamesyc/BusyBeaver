module
public import I3_380.Search.Compiler.Reference
public import I3_380.Engine.Arithmetic.FrameExecution
public import I3_380.Engine.Arithmetic.ReferenceStartup
@[expose] public section

namespace PalomarI3380.Compiler

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine (Reaches)
open ArithmeticMachine.Reference (Frame Outcome ReachesHalt)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def projectFrame (s : Frame M) : PathState M := project s.logical

/-- Selection and pointer motion implement exactly the program's
next operation, also on nonstandard register values. -/
theorem frame_step (s : Frame M) (ready : s.Prepared) :
    ((ArithmeticMachine.Reference.execute s).logical.map project) =
      step referenceProgram (projectFrame s) := by
  rw [ArithmeticMachine.Reference.logical_projection]
  exact project_reference_step s.logical (le_trans (by decide : 12 ≤ 13) ready.2.1)

theorem advance_frame {s : Frame M} (ready : s.Prepared) {t : PathState M}
    (edge : step referenceProgram (projectFrame s) = some t) :
    ∃ target : Frame M, ArithmeticMachine.Reference.execute s = .next target ∧
      Reaches referenceMachine s.code target.code ∧ target.Prepared ∧ projectFrame target = t := by
  have simulation := frame_step s ready
  have sound := ArithmeticMachine.Reference.execute_realizes s ready
  rw [edge] at simulation
  cases out : ArithmeticMachine.Reference.execute s with
  | invalid | halt => simp [out,Outcome.logical] at simulation
  | next target =>
    rw [out] at sound simulation
    refine ⟨target,rfl,sound.1,sound.2,?_⟩
    exact Option.some.inj simulation

theorem halt_frame {s : Frame M} (ready : s.Prepared)
    (terminal : step referenceProgram (projectFrame s) = none) :
    ReachesHalt s.code := by
  have simulation := frame_step s ready
  have sound := ArithmeticMachine.Reference.execute_realizes s ready
  rw [terminal] at simulation
  cases out : ArithmeticMachine.Reference.execute s with
  | invalid => rw [out] at sound; exact sound.elim
  | halt => rwa [out] at sound
  | next target => simp [out,Outcome.logical] at simulation

end PalomarI3380.Compiler
