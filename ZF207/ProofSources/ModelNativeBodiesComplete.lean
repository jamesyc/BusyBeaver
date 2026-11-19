module
public import ModelNativeMPCommand
public import ModelNativeAXCommand
public import ModelNativeSummaryHistory
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeCommands
open ZF207.NativeSource ZF207.ModelCommands ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- The full native body contract, with no remaining operational premises. -/
theorem successBodyContract_proved : successBodyContract (M:=M) := by
 intro c n tail s out he
 cases c with
 | shift=>
  have hh:=native_shift_command n tail s
  rw [he] at hh
  exact hh
 | mp x=>exact NativeMP.native_mp_command n tail x s out he
 | ax a x y=>exact NativeAXCommand.native_ax_command n tail a x y s out he
end ZF207.NativeCommands
