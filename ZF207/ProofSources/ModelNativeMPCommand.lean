module
public import ModelNativeMPSuffix
public import ModelNativeMPGuard
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeMP
open ZF207.NativeSource ZF207.NativeCommands ZFR.ArithmeticRepresentation ZF207.ModelCommands ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem native_mp_command (n tail x:M) (s out:Store M)
 (he:modelCommandEval (.mp x) s=some out) :
 nativeReaches (bodyEntry (.mp x) n tail s) (commandState 25 n tail 0 out) := by
 rcases s with ⟨t,w,d,h⟩
 have hp:=native_mp_prefix n tail t w d h x
 have hg:=NativeMPGuard.native_mp_guard n tail (t299 t (d+x)) w (d+x) h
 by_cases hc:t299 t (d+x)=h
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
end ZF207.NativeMP
