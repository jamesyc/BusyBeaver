module
public import ModelResidualTransferLoop
public import ModelNativeUnpairRound
public import ModelResidualRestoreYLoop
public import ModelResidualRestoreXLoop
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ResidualSource
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano M207.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def unpairState (ρ:Nat→M) (pc w h x y:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,w,ρ 2,ρ 3,h,y,ρ 6,ρ 7,x]⟩
lemma unpair_step11_zero (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 34 0 h x y) (unpairState ρ 42 0 h x y) := by
 refine ⟨34,by decide,by simp [unpairState],.dec 1 42 35,by decide,?_⟩
 simp [NativeSource.execute,unpairState,registerIndex]
lemma unpair_step11_dec (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 34 (w+1) h x y) (unpairState ρ 35 w h x y) := by
 refine ⟨34,by decide,by simp [unpairState],.dec 1 42 35,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (unpairState ρ 34 (w+1) h x y).registers (registerIndex 1)≠0 from by change w+1≠0; simp)]
 change some ⟨(35:M),fun j=>if j.val=1 then modelPredecessor ((unpairState ρ 34 (w+1) h x y).registers j) else (unpairState ρ 34 (w+1) h x y).registers j⟩=some (unpairState ρ 35 w h x y)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [unpairState,modelPredecessor_succ]
lemma unpair_step12_inc (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 35 w h x y) (unpairState ρ 36 w h x (y+1)) := by
 refine ⟨35,by decide,by simp [unpairState],.inc 5 36,by decide,?_⟩
 simp only [NativeSource.execute,unpairState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [unpairState,modelPredecessor_succ]
lemma unpair_step13_zero (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 36 w h 0 y) (unpairState ρ 38 w h 0 y) := by
 refine ⟨36,by decide,by simp [unpairState],.dec 8 38 37,by decide,?_⟩
 simp [NativeSource.execute,unpairState,registerIndex]
lemma unpair_step13_dec (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 36 w h (x+1) y) (unpairState ρ 37 w h x y) := by
 refine ⟨36,by decide,by simp [unpairState],.dec 8 38 37,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (unpairState ρ 36 w h (x+1) y).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 change some ⟨(37:M),fun j=>if j.val=8 then modelPredecessor ((unpairState ρ 36 w h (x+1) y).registers j) else (unpairState ρ 36 w h (x+1) y).registers j⟩=some (unpairState ρ 37 w h x y)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [unpairState,modelPredecessor_succ]
lemma unpair_step14_jump (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 37 w h x y) (unpairState ρ 41 w h x y) := by
 refine ⟨37,by decide,by simp [unpairState],.jump 41,by decide,?_⟩
 simp [NativeSource.execute,unpairState,registerIndex]
lemma unpair_step18_jump (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 41 w h x y) (unpairState ρ 34 w h x y) := by
 refine ⟨41,by decide,by simp [unpairState],.jump 34,by decide,?_⟩
 simp [NativeSource.execute,unpairState,registerIndex]
lemma unpair_round_positive (ρ:Nat→M) (w h x y:M) :
 nativeReaches (unpairState ρ 34 (w+1) h (x+1) y) (unpairState ρ 34 w h x (y+1)) := by
 apply nativeReaches_trans (nativeReaches_step (unpair_step11_dec ρ w h (x+1) y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step12_inc ρ w h (x+1) y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step13_dec ρ w h x (y+1)))
 exact nativeReaches_trans (nativeReaches_step (unpair_step14_jump ρ w h x (y+1)))
   (nativeReaches_step (unpair_step18_jump ρ w h x (y+1)))
lemma unpair_transfer (ρ:Nat→M) (w h x y:M) :
 nativeReaches (unpairState ρ 38 w h x y) (unpairState ρ 41 w h (x+y) 0) := by
 let frame:Nat→M:=fun i=>if i=1 then w else if i=4 then h else ρ i
 have ht:=transfer_terminates frame y x
 simpa [transferTerminates,nativeReaches,transferState,unpairState,frame] using ht
lemma unpair_round_zero (ρ:Nat→M) (w h y:M) :
 nativeReaches (unpairState ρ 34 (w+1) h 0 y) (unpairState ρ 34 w h (y+1) 0) := by
 apply nativeReaches_trans (nativeReaches_step (unpair_step11_dec ρ w h 0 y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step12_inc ρ w h 0 y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step13_zero ρ w h 0 (y+1)))
 have ht:=unpair_transfer ρ w h 0 (y+1)
 simp only [zero_add] at ht
 exact nativeReaches_trans ht (nativeReaches_step (unpair_step18_jump ρ w h (y+1) 0))
end ZF207.ResidualSource
