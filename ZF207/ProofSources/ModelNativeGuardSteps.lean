module
public import ModelNativeFetchSteps
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeGuard
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano M207.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def guardState (ρ:Nat→M) (pc h x:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,ρ 1,ρ 2,ρ 3,ρ 4,ρ 5,ρ 6,h,x]⟩
lemma step0_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 0 0 x) (guardState ρ 4 0 x) := by
 refine ⟨0,by decide,by simp [guardState],.dec 7 4 1,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step0_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 0 (h+1) x) (guardState ρ 1 h x) := by
 refine ⟨0,by decide,by simp [guardState],.dec 7 4 1,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 0 (h+1) x).registers (registerIndex 7)≠0 from by change h+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(1:M),fun j=>if j.val=7 then modelPredecessor ((guardState ρ 0 (h+1) x).registers j) else (guardState ρ 0 (h+1) x).registers j⟩=some (guardState ρ 1 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step1_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 1 h 0) (guardState ρ 3 h 0) := by
 refine ⟨1,by decide,by simp [guardState],.dec 8 3 2,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step1_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 1 h (x+1)) (guardState ρ 2 h x) := by
 refine ⟨1,by decide,by simp [guardState],.dec 8 3 2,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 1 h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(2:M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ 1 h (x+1)).registers j) else (guardState ρ 1 h (x+1)).registers j⟩=some (guardState ρ 2 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step2 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 2 h x) (guardState ρ 0 h x) := by
 refine ⟨2,by decide,by simp [guardState],.jump 0,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step3 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 3 h x) (guardState ρ 5 h x) := by
 refine ⟨3,by decide,by simp [guardState],.jump 5,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4 h 0) (guardState ρ 10 h 0) := by
 refine ⟨4,by decide,by simp [guardState],.dec 8 10 5,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4 h (x+1)) (guardState ρ 5 h x) := by
 refine ⟨4,by decide,by simp [guardState],.dec 8 10 5,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4 h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(5:M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ 4 h (x+1)).registers j) else (guardState ρ 4 h (x+1)).registers j⟩=some (guardState ρ 5 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step5_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 5 0 x) (guardState ρ 7 0 x) := by
 refine ⟨5,by decide,by simp [guardState],.dec 7 7 6,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step5_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 5 (h+1) x) (guardState ρ 6 h x) := by
 refine ⟨5,by decide,by simp [guardState],.dec 7 7 6,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 5 (h+1) x).registers (registerIndex 7)≠0 from by change h+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(6:M),fun j=>if j.val=7 then modelPredecessor ((guardState ρ 5 (h+1) x).registers j) else (guardState ρ 5 (h+1) x).registers j⟩=some (guardState ρ 6 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step6 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 6 h x) (guardState ρ 5 h x) := by
 refine ⟨6,by decide,by simp [guardState],.jump 5,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step7_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 7 h 0) (guardState ρ 9 h 0) := by
 refine ⟨7,by decide,by simp [guardState],.dec 8 9 8,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step7_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 7 h (x+1)) (guardState ρ 8 h x) := by
 refine ⟨7,by decide,by simp [guardState],.dec 8 9 8,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 7 h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(8:M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ 7 h (x+1)).registers j) else (guardState ρ 7 h (x+1)).registers j⟩=some (guardState ρ 8 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step8 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 8 h x) (guardState ρ 5 h x) := by
 refine ⟨8,by decide,by simp [guardState],.jump 5,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step9 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 9 h x) (guardState ρ 11 h x) := by
 refine ⟨9,by decide,by simp [guardState],.jump 11,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]

end ZF207.NativeGuard
