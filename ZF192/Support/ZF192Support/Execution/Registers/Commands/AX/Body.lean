module
public import ZF192Support.Execution.Registers.Commands.AX.Prefix
public import ZF192Support.Execution.Registers.Commands.AX.Gate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeAXCommand
open ZF192Support.Internal (imp mem eqc all)
open ZFR.ArithmeticRepresentation ZF192Support.ModelCommands ZF192Support.NativeSource ZF192Support.NativeCommands
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem native_ax_command (n tail a x y:M) (s out:ModelCommands.Store M)
 (he:modelCommandEval (.ax a x y) s=some out) :
 nativeReaches (bodyEntry (.ax a x y) n tail s) (commandState 25 n tail 0 out) := by
 rcases s with ⟨t,w,d,h⟩
 have ho:out=⟨gate a (d+x) (h+y),(heads a (d+x) (h+y) d h++[t]).foldr modelCantor w,0,0⟩:=by
  simpa only [modelCommandEval,Option.some.injEq] using he.symm
 subst out
 have hp:=NativeAXSymbolic.native_ax_prefix n tail t w d h a x y
 have hg:=NativeAXGate.native_ax_gate n
  (⟨axGate a (d+x) (h+y),a,d+x,h+y,tail,(heads a (d+x) (h+y) d h++[t]).foldr modelCantor w⟩ : NativeAX.Store M)
 exact nativeReaches_trans hp hg
end ZF192Support.NativeAXCommand
