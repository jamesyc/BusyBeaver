module
public import ModelAXFieldHTransferLoop
public import ModelNativeUnpairRound
public import ModelAXFieldHRestoreYLoop
public import ModelAXFieldHRestoreXLoop
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.AXFieldHSource
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano M207.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def unpairState (ρ:Nat→M) (pc w h x y:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,w,ρ 2,ρ 3,ρ 4,y,ρ 6,h,x]⟩
lemma unpair_step11_zero (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 131 0 h x y) (unpairState ρ 139 0 h x y) := by
 refine ⟨131,by decide,by simp [unpairState],.dec 1 139 132,by decide,?_⟩
 simp [NativeSource.execute,unpairState,registerIndex]
lemma unpair_step11_dec (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 131 (w+1) h x y) (unpairState ρ 132 w h x y) := by
 refine ⟨131,by decide,by simp [unpairState],.dec 1 139 132,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (unpairState ρ 131 (w+1) h x y).registers (registerIndex 1)≠0 from by change w+1≠0; simp)]
 change some ⟨(132:M),fun j=>if j.val=1 then modelPredecessor ((unpairState ρ 131 (w+1) h x y).registers j) else (unpairState ρ 131 (w+1) h x y).registers j⟩=some (unpairState ρ 132 w h x y)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [unpairState,modelPredecessor_succ]
lemma unpair_step12_inc (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 132 w h x y) (unpairState ρ 133 w h x (y+1)) := by
 refine ⟨132,by decide,by simp [unpairState],.inc 5 133,by decide,?_⟩
 simp only [NativeSource.execute,unpairState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [unpairState,modelPredecessor_succ]
lemma unpair_step13_zero (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 133 w h 0 y) (unpairState ρ 135 w h 0 y) := by
 refine ⟨133,by decide,by simp [unpairState],.dec 8 135 134,by decide,?_⟩
 simp [NativeSource.execute,unpairState,registerIndex]
lemma unpair_step13_dec (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 133 w h (x+1) y) (unpairState ρ 134 w h x y) := by
 refine ⟨133,by decide,by simp [unpairState],.dec 8 135 134,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (unpairState ρ 133 w h (x+1) y).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 change some ⟨(134:M),fun j=>if j.val=8 then modelPredecessor ((unpairState ρ 133 w h (x+1) y).registers j) else (unpairState ρ 133 w h (x+1) y).registers j⟩=some (unpairState ρ 134 w h x y)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [unpairState,modelPredecessor_succ]
lemma unpair_step14_jump (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 134 w h x y) (unpairState ρ 138 w h x y) := by
 refine ⟨134,by decide,by simp [unpairState],.jump 138,by decide,?_⟩
 simp [NativeSource.execute,unpairState,registerIndex]
lemma unpair_step18_jump (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 138 w h x y) (unpairState ρ 131 w h x y) := by
 refine ⟨138,by decide,by simp [unpairState],.jump 131,by decide,?_⟩
 simp [NativeSource.execute,unpairState,registerIndex]
lemma unpair_round_positive (ρ:Nat→M) (w h x y:M) :
 nativeReaches (unpairState ρ 131 (w+1) h (x+1) y) (unpairState ρ 131 w h x (y+1)) := by
 apply nativeReaches_trans (nativeReaches_step (unpair_step11_dec ρ w h (x+1) y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step12_inc ρ w h (x+1) y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step13_dec ρ w h x (y+1)))
 exact nativeReaches_trans (nativeReaches_step (unpair_step14_jump ρ w h x (y+1)))
   (nativeReaches_step (unpair_step18_jump ρ w h x (y+1)))
lemma unpair_transfer (ρ:Nat→M) (w h x y:M) :
 nativeReaches (unpairState ρ 135 w h x y) (unpairState ρ 138 w h (x+y) 0) := by
 let frame:Nat→M:=fun i=>if i=1 then w else if i=7 then h else ρ i
 have ht:=transfer_terminates frame y x
 simpa [transferTerminates,nativeReaches,transferState,unpairState,frame] using ht
lemma unpair_round_zero (ρ:Nat→M) (w h y:M) :
 nativeReaches (unpairState ρ 131 (w+1) h 0 y) (unpairState ρ 131 w h (y+1) 0) := by
 apply nativeReaches_trans (nativeReaches_step (unpair_step11_dec ρ w h 0 y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step12_inc ρ w h 0 y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step13_zero ρ w h 0 (y+1)))
 have ht:=unpair_transfer ρ w h 0 (y+1)
 simp only [zero_add] at ht
 exact nativeReaches_trans ht (nativeReaches_step (unpair_step18_jump ρ w h (y+1) 0))
end ZF207.AXFieldHSource
