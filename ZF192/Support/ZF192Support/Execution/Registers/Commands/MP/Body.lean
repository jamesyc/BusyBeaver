module
public import ZF192Support.Execution.Registers.Commands.MP.Suffix
public import ZF192Support.Execution.Registers.Commands.MP.Guard
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeMP
open ZF192Support.Internal (imp mem eqc all)
open ZF192Support.NativeSource ZF192Support.NativeCommands ZFR.ArithmeticRepresentation ZF192Support.ModelCommands
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem native_mp_command (n tail x:M) (s out:Store M)
 (he:modelCommandEval (.mp x) s=some out) :
 nativeReaches (bodyEntry (.mp x) n tail s) (commandState 25 n tail 0 out) := by
 rcases s with ⟨t,w,d,h⟩
 have hp:=native_mp_prefix n tail t w d h x
 have hg:=NativeMPGuard.native_mp_guard n tail (imp t (d+x)) w (d+x) h
 by_cases hc:imp t (d+x)=h
 · rw [if_pos hc] at hg
   have ho:out=⟨d+x,modelCantor 0 w,d+x,0⟩:=by
    simpa [modelCommandEval,hc] using he.symm
   subst out
   exact nativeReaches_trans hp (nativeReaches_trans hg (success n tail w (d+x)))
 · rw [if_neg hc] at hg
   have ho:out=⟨0,w,d+x,0⟩:=by
    simpa [modelCommandEval,hc] using he.symm
   subst out
   exact nativeReaches_trans hp (nativeReaches_trans hg (return_to_fetch n tail 0 w (d+x) 0))
end ZF192Support.NativeMP
