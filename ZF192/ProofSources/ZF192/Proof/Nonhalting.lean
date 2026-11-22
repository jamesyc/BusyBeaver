module
public import ZF192.Simulation.Standard.Endpoint
public import ZF192Support.Execution.Registers.Scheduler.Soundness
public import ZF192.Simulation.Forward.Startup
public import ZF192.Tape.Halting.StandardModel
public import ZF192Support.SetTheory.CalculusSoundness
public import ZF192Support.Calculus.Internal.StandardTrace
public import ZF192Support.SetTheory.ModelExistence

@[expose] public section
namespace ZF192

open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory
open ZF192Support.Halting
open CCodeSoundness RegisterMachine.Source RegisterMachine.SourceSimulation
open ZF192Support.NativeCommands

theorem literal_halts_iff_refutation :
    BinaryTape.Halts M192.literal (BinaryTape.zc 0 [] []) ↔ ExactProvable 1 := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    rw [M192.Source.blank_halts_iff_nine_register_cfg] at h
    exact native_initial_nonterminates hn h
  · intro h
    obtain ⟨p, hp, hm⟩ := trace_of_exactProvable h
    exact ZF192.BinaryTape.physicalHalts_nat_iff.mp
      (ZF192.NativePhysicalLift.literalCRefutation_physical
        (ZF192Support.ModelCommands.refutation_compilable p hp hm))

/-- In the standard natural numbers, the exact blank-tape machine runs forever
if ordinary first-order ZF is consistent. -/
theorem literal192_nonhalting_of_foundation_consistent
    [FFL.Entailment.Consistent (𝗭𝗙 : SetTheory)] :
    ¬ BinaryTape.Halts M192.literal (BinaryTape.zc 0 [] []) := by
  intro h
  obtain ⟨V, _, _, _⟩ := ZF192Support.Independence.exists_zf_model
  exact (evalCode_one_false (fun a b : V => a ∈ b) (fun x => mem_irrefl x) (fun _ => ∅)).mp
    (exact_true (literal_halts_iff_refutation.mp h) (fun _ => (∅ : V)))

end ZF192
