module
public import ModelNativeSTransfer
public import ModelNativeSRestore
public import ModelNativeSDrain
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeSStage
open ZF207.NativeSource ZFR.ArithmeticRepresentation M207.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def stageState (ρ:Nat→M) (pc t h x:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,ρ 1,t,ρ 3,ρ 4,ρ 5,ρ 6,h,x]⟩
lemma stage_transfer (ρ:Nat→M) (t h x:M) : nativeReaches (stageState ρ 4329 t h x) (stageState ρ 4332 0 h (x+t)) := by
 let frame:Nat→M:=fun i=>if i=7 then h else ρ i
 have ht:=NativeSTransfer.transfer_terminates frame t x
 simpa [NativeSTransfer.transferTerminates,NativeSTransfer.transferState,stageState,nativeReaches,frame] using ht
lemma stage_drain (ρ:Nat→M) (t h x:M) : nativeReaches (stageState ρ 4332 t h x) (stageState ρ 4336 (t+h) 0 (x+h)) := by
 have ht:=NativeSDrain.drain_terminates ρ h t x
 exact ht
lemma stage_restore (ρ:Nat→M) (t h x:M) : nativeReaches (stageState ρ 4336 t h x) (stageState ρ 4339 t (h+x) 0) := by
 let frame:Nat→M:=fun i=>if i=2 then t else ρ i
 have ht:=NativeSRestore.restoreX_terminates frame x h
 simpa [NativeSRestore.restoreXTerminates,NativeSRestore.restoreXState,stageState,nativeReaches,frame] using ht
lemma stage_inc (ρ:Nat→M) (t h x:M) : programStep (stageState ρ 4339 t h x) (stageState ρ 4340 t h (x+1)) := by
 refine ⟨4339,by decide,by simp [stageState],.inc 8 4340,by decide,?_⟩
 simp only [NativeSource.execute,stageState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp
lemma stage_jump (ρ:Nat→M) (t h x:M) : programStep (stageState ρ 4340 t h x) (stageState ρ 0 t h x) := by
 refine ⟨4340,by decide,by simp [stageState],.jump 0,by decide,?_⟩
 simp [NativeSource.execute,stageState]
/-- Exact literal SHIFT staging, before shared equality guard. -/
theorem native_shift_stage (ρ:Nat→M) (t h:M) : nativeReaches (stageState ρ 4329 t h 0) (stageState ρ 0 h (t+h) 1) := by
 have h1:=stage_transfer ρ t h 0
 rw [zero_add] at h1
 have h2:=stage_drain ρ 0 h t
 rw [zero_add] at h2
 have h3:=stage_restore ρ h 0 (t+h)
 rw [zero_add] at h3
 have h4:=stage_inc ρ h (t+h) 0
 rw [zero_add] at h4
 exact nativeReaches_trans h1 (nativeReaches_trans h2 (nativeReaches_trans h3
  (nativeReaches_trans (nativeReaches_step h4) (nativeReaches_step (stage_jump ρ h (t+h) 1)))))
end ZF207.NativeSStage
