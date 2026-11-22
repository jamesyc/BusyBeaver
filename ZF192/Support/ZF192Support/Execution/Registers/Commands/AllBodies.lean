module
public import ZF192Support.Execution.Registers.Commands.MP.Body
public import ZF192Support.Execution.Registers.Commands.AX.Body
public import ZF192Support.Execution.Registers.Scheduler.SummaryHistory
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeCommands
open ZF192Support.NativeSource ZF192Support.ModelCommands ZFR.ArithmeticRepresentation
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
end ZF192Support.NativeCommands
