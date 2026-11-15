module
public import ModelNativeFetchSteps
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeAXCompareD
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def guardState (ρ:Nat→M) (pc h x:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,ρ 1,ρ 2,ρ 3,ρ 4,ρ 5,ρ 6,h,x]⟩
lemma step4209_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4209 0 x) (guardState ρ 4213 0 x) := by
 refine ⟨4209,by decide,by simp [guardState],.dec 7 4213 4210,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4209_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4209 (h+1) x) (guardState ρ 4210 h x) := by
 refine ⟨4209,by decide,by simp [guardState],.dec 7 4213 4210,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4209 (h+1) x).registers (registerIndex 7)≠0 from by change h+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4210:M),fun j=>if j.val=7 then modelPredecessor ((guardState ρ 4209 (h+1) x).registers j) else (guardState ρ 4209 (h+1) x).registers j⟩=some (guardState ρ 4210 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4210_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4210 h 0) (guardState ρ 4212 h 0) := by
 refine ⟨4210,by decide,by simp [guardState],.dec 8 4212 4211,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4210_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4210 h (x+1)) (guardState ρ 4211 h x) := by
 refine ⟨4210,by decide,by simp [guardState],.dec 8 4212 4211,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4210 h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4211:M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ 4210 h (x+1)).registers j) else (guardState ρ 4210 h (x+1)).registers j⟩=some (guardState ρ 4211 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4211 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4211 h x) (guardState ρ 4209 h x) := by
 refine ⟨4211,by decide,by simp [guardState],.jump 4209,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4212 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4212 h x) (guardState ρ 4214 h x) := by
 refine ⟨4212,by decide,by simp [guardState],.jump 4214,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4213_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4213 h 0) (guardState ρ 4219 h 0) := by
 refine ⟨4213,by decide,by simp [guardState],.dec 8 4219 4214,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4213_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4213 h (x+1)) (guardState ρ 4214 h x) := by
 refine ⟨4213,by decide,by simp [guardState],.dec 8 4219 4214,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4213 h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4214:M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ 4213 h (x+1)).registers j) else (guardState ρ 4213 h (x+1)).registers j⟩=some (guardState ρ 4214 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4214_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4214 0 x) (guardState ρ 4216 0 x) := by
 refine ⟨4214,by decide,by simp [guardState],.dec 7 4216 4215,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4214_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4214 (h+1) x) (guardState ρ 4215 h x) := by
 refine ⟨4214,by decide,by simp [guardState],.dec 7 4216 4215,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4214 (h+1) x).registers (registerIndex 7)≠0 from by change h+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4215:M),fun j=>if j.val=7 then modelPredecessor ((guardState ρ 4214 (h+1) x).registers j) else (guardState ρ 4214 (h+1) x).registers j⟩=some (guardState ρ 4215 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4215 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4215 h x) (guardState ρ 4214 h x) := by
 refine ⟨4215,by decide,by simp [guardState],.jump 4214,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4216_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4216 h 0) (guardState ρ 4218 h 0) := by
 refine ⟨4216,by decide,by simp [guardState],.dec 8 4218 4217,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4216_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4216 h (x+1)) (guardState ρ 4217 h x) := by
 refine ⟨4216,by decide,by simp [guardState],.dec 8 4218 4217,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4216 h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4217:M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ 4216 h (x+1)).registers j) else (guardState ρ 4216 h (x+1)).registers j⟩=some (guardState ρ 4217 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4217 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4217 h x) (guardState ρ 4214 h x) := by
 refine ⟨4217,by decide,by simp [guardState],.jump 4214,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4218 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4218 h x) (guardState ρ 4221 h x) := by
 refine ⟨4218,by decide,by simp [guardState],.jump 4221,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]

end ZF209.NativeAXCompareD
