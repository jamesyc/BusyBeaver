module
public import ModelNativeFrameContracts
public import M209.SourceData
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape.FrameCoverage
open M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def CoverageAt (i:Nat) : Prop := ∃code,program i=some code ∧ FrameImplements (M:=M) i code
end ZF209.BinaryTape.FrameCoverage
