module
public import ModelNativeFetchSteps
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeAXCompareH
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def guardState (ρ:Nat→M) (pc h x:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,ρ 1,ρ 2,ρ 3,ρ 4,ρ 5,ρ 6,h,x]⟩
lemma step4191_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4191 0 x) (guardState ρ 4195 0 x) := by
 refine ⟨4191,by decide,by simp [guardState],.dec 7 4195 4192,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4191_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4191 (h+1) x) (guardState ρ 4192 h x) := by
 refine ⟨4191,by decide,by simp [guardState],.dec 7 4195 4192,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4191 (h+1) x).registers (registerIndex 7)≠0 from by change h+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4192:M),fun j=>if j.val=7 then modelPredecessor ((guardState ρ 4191 (h+1) x).registers j) else (guardState ρ 4191 (h+1) x).registers j⟩=some (guardState ρ 4192 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4192_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4192 h 0) (guardState ρ 4194 h 0) := by
 refine ⟨4192,by decide,by simp [guardState],.dec 8 4194 4193,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4192_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4192 h (x+1)) (guardState ρ 4193 h x) := by
 refine ⟨4192,by decide,by simp [guardState],.dec 8 4194 4193,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4192 h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4193:M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ 4192 h (x+1)).registers j) else (guardState ρ 4192 h (x+1)).registers j⟩=some (guardState ρ 4193 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4193 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4193 h x) (guardState ρ 4191 h x) := by
 refine ⟨4193,by decide,by simp [guardState],.jump 4191,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4194 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4194 h x) (guardState ρ 4196 h x) := by
 refine ⟨4194,by decide,by simp [guardState],.jump 4196,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4195_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4195 h 0) (guardState ρ 4201 h 0) := by
 refine ⟨4195,by decide,by simp [guardState],.dec 8 4201 4196,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4195_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4195 h (x+1)) (guardState ρ 4196 h x) := by
 refine ⟨4195,by decide,by simp [guardState],.dec 8 4201 4196,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4195 h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4196:M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ 4195 h (x+1)).registers j) else (guardState ρ 4195 h (x+1)).registers j⟩=some (guardState ρ 4196 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4196_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4196 0 x) (guardState ρ 4198 0 x) := by
 refine ⟨4196,by decide,by simp [guardState],.dec 7 4198 4197,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4196_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4196 (h+1) x) (guardState ρ 4197 h x) := by
 refine ⟨4196,by decide,by simp [guardState],.dec 7 4198 4197,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4196 (h+1) x).registers (registerIndex 7)≠0 from by change h+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4197:M),fun j=>if j.val=7 then modelPredecessor ((guardState ρ 4196 (h+1) x).registers j) else (guardState ρ 4196 (h+1) x).registers j⟩=some (guardState ρ 4197 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4197 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4197 h x) (guardState ρ 4196 h x) := by
 refine ⟨4197,by decide,by simp [guardState],.jump 4196,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4198_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4198 h 0) (guardState ρ 4200 h 0) := by
 refine ⟨4198,by decide,by simp [guardState],.dec 8 4200 4199,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4198_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4198 h (x+1)) (guardState ρ 4199 h x) := by
 refine ⟨4198,by decide,by simp [guardState],.dec 8 4200 4199,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4198 h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4199:M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ 4198 h (x+1)).registers j) else (guardState ρ 4198 h (x+1)).registers j⟩=some (guardState ρ 4199 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4199 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4199 h x) (guardState ρ 4196 h x) := by
 refine ⟨4199,by decide,by simp [guardState],.jump 4196,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4200 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4200 h x) (guardState ρ 4203 h x) := by
 refine ⟨4200,by decide,by simp [guardState],.jump 4203,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]

end ZF209.NativeAXCompareH
