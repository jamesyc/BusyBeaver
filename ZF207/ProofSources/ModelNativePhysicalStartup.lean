module
public import ModelNativeInitial
public import ModelPhysicalNatEquivalence
public import ModelRegisterFileEncoding
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Exact physical startup endpoint of the published literal207 table. -/
noncomputable def physicalStartupEnd : ZF207.BinaryTape.State M :=
 ZF207.BinaryTape.encode (M207.Source.frame M207.Source.paths M207.Source.initialState)
/-- The checked fixed58616-step prefix yields an actual internally coded physical
history in EVERY PA model, rather than merely an external Nat halting fact. -/
theorem physical_startup_prefix : ∃hist:M,
 ZF207.BinaryTape.runHistory ZF207.BinaryTape.blankCode hist ∧
 modelListHead hist=ZF207.BinaryTape.stateCode physicalStartupEnd := by
 have h:=ZF207.BinaryTape.physical_reach_history (M:=M) (M6.Zip.zc 0 [] [])
  (M207.Source.frame M207.Source.paths M207.Source.initialState) M207.Source.blank_to_cfg
 simpa only [ZF207.BinaryTape.blankCode_encoded,physicalStartupEnd] using h
end ZF207.NativeCommands
