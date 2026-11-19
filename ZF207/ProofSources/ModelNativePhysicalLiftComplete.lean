module
public import ModelNativeFrameStep
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativePhysicalLift
open ZFR.ArithmeticRepresentation ZF207.NativeSource ZF207.BinaryTape
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def Coverage : Prop := ∀pc:Nat,pc<4341→∃code,M207.Source.program pc=some code ∧ FrameImplements (M:=M) pc code
theorem frame_history_lift (coverage:Coverage (M:=M)) (initial code:M) :
 Simulation FrameRelation initial code :=
 native_history_lift frameRelationGraph FrameRelation frameRelationGraph_eval (frame_step_contract coverage) initial code
end ZF207.NativePhysicalLift
