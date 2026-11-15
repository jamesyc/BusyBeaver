module
public import ModelCRefutationPhysicalCore
public import ModelFrameCoverageComplete
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativePhysicalLift
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Exact literal209 physical halting, with all native body and4341site
simulation obligations discharged. The source-ZF→C calibration is separate. -/
theorem literalCRefutation_physical (h:ZF209.ModelCommands.compilable (1:M)) :
 BinaryTape.physicalHalts (M:=M) :=
 literalCRefutation_physical_of_coverage BinaryTape.FrameCoverage.complete h
end ZF209.NativePhysicalLift
