module
public import ModelNativeFrameStep
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativePhysicalLift
open ZFR.ArithmeticRepresentation ZF209.NativeSource ZF209.BinaryTape
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def Coverage : Prop := ∀pc:Nat,pc<4341→∃code,M209.Source.program pc=some code ∧ FrameImplements (M:=M) pc code
theorem frame_history_lift (coverage:Coverage (M:=M)) (initial code:M) :
 Simulation FrameRelation initial code :=
 native_history_lift frameRelationGraph FrameRelation frameRelationGraph_eval (frame_step_contract coverage) initial code
end ZF209.NativePhysicalLift
