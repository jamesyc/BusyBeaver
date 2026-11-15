module
public import ModelNativeInitial
public import ModelPhysicalNatEquivalence
public import ModelRegisterFileEncoding
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Exact physical startup endpoint of the published literal209 table. -/
noncomputable def physicalStartupEnd : ZF209.BinaryTape.State M :=
 ZF209.BinaryTape.encode (M209.Source.frame M209.Source.paths M209.Source.initialState)
/-- The checked fixed58154-step prefix yields an actual internally coded physical
history in EVERY PA model, rather than merely an external Nat halting fact. -/
theorem physical_startup_prefix : ∃hist:M,
 ZF209.BinaryTape.runHistory ZF209.BinaryTape.blankCode hist ∧
 modelListHead hist=ZF209.BinaryTape.stateCode physicalStartupEnd := by
 have h:=ZF209.BinaryTape.physical_reach_history (M:=M) (M6.Zip.zc 0 [] [])
  (M209.Source.frame M209.Source.paths M209.Source.initialState) M209.Source.blank_to_cfg
 simpa only [ZF209.BinaryTape.blankCode_encoded,physicalStartupEnd] using h
end ZF209.NativeCommands
