module
public import ModelMPFieldUnpairLoop
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MPFieldSource
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma unpair_restoreY (ρ:Nat→M) (w h x y:M) :
 nativeReaches (unpairState ρ 4230 w h x y) (unpairState ρ 4233 (w+y) h x 0) := by
 let frame:Nat→M:=fun i=>if i=3 then h else if i=8 then x else ρ i
 have ht:=restoreY_terminates frame y w
 simpa [restoreYTerminates,nativeReaches,restoreYState,unpairState,frame] using ht
lemma unpair_restoreX (ρ:Nat→M) (w h x y:M) :
 nativeReaches (unpairState ρ 4233 w h x y) (unpairState ρ 4236 w (h+x) 0 y) := by
 let frame:Nat→M:=fun i=>if i=1 then w else if i=5 then y else ρ i
 have ht:=restoreX_terminates frame x h
 simpa [restoreXTerminates,nativeReaches,restoreXState,unpairState,frame] using ht
/-- Full literal native unpair macro, valid for arbitrary PA-model input n.
All five unmentioned scalar registers stay arbitrary and unchanged. -/
theorem native_unpair (ρ:Nat→M) (n:M) :
 nativeReaches (unpairState ρ 4222 n 0 0 0)
 (unpairState ρ 4236 (modelUnpairRight n) (modelUnpairLeft n) 0 0) := by
 have body:=unpair_loop_terminates ρ n 0 0 0
 change nativeReaches _ (unpairState ρ 4230 0 0 (modelUnpairLeft (n+modelCantor 0 0)) (modelUnpairRight (n+modelCantor 0 0))) at body
 rw [modelCantor_zero,add_zero] at body
 have hy:=unpair_restoreY ρ 0 0 (modelUnpairLeft n) (modelUnpairRight n)
 rw [zero_add] at hy
 have hx:=unpair_restoreX ρ (modelUnpairRight n) 0 (modelUnpairLeft n) 0
 rw [zero_add] at hx
 exact nativeReaches_trans body (nativeReaches_trans hy hx)
theorem native_unpair_add (ρ:Nat→M) (n h:M) :
 nativeReaches (unpairState ρ 4222 n h 0 0)
 (unpairState ρ 4236 (modelUnpairRight n) (h+modelUnpairLeft n) 0 0) := by
 have body:=unpair_loop_terminates ρ n h 0 0
 change nativeReaches _ (unpairState ρ 4230 0 h (modelUnpairLeft (n+modelCantor 0 0)) (modelUnpairRight (n+modelCantor 0 0))) at body
 rw [modelCantor_zero,add_zero] at body
 have hy:=unpair_restoreY ρ 0 h (modelUnpairLeft n) (modelUnpairRight n)
 rw [zero_add] at hy
 have hx:=unpair_restoreX ρ (modelUnpairRight n) h (modelUnpairLeft n) 0
 exact nativeReaches_trans body (nativeReaches_trans hy hx)
end ZF209.MPFieldSource
