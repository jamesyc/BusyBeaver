module
public import ModelNativeFetchSteps
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeMPCompare
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano M207.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def guardState (ρ:Nat→M) (pc h x:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,ρ 1,ρ 2,ρ 3,ρ 4,ρ 5,ρ 6,h,x]⟩
lemma step4292_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4292 0 x) (guardState ρ 4296 0 x) := by
 refine ⟨4292,by decide,by simp [guardState],.dec 7 4296 4293,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4292_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4292 (h+1) x) (guardState ρ 4293 h x) := by
 refine ⟨4292,by decide,by simp [guardState],.dec 7 4296 4293,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4292 (h+1) x).registers (registerIndex 7)≠0 from by change h+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4293:M),fun j=>if j.val=7 then modelPredecessor ((guardState ρ 4292 (h+1) x).registers j) else (guardState ρ 4292 (h+1) x).registers j⟩=some (guardState ρ 4293 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4293_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4293 h 0) (guardState ρ 4295 h 0) := by
 refine ⟨4293,by decide,by simp [guardState],.dec 8 4295 4294,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4293_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4293 h (x+1)) (guardState ρ 4294 h x) := by
 refine ⟨4293,by decide,by simp [guardState],.dec 8 4295 4294,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4293 h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4294:M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ 4293 h (x+1)).registers j) else (guardState ρ 4293 h (x+1)).registers j⟩=some (guardState ρ 4294 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4294 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4294 h x) (guardState ρ 4292 h x) := by
 refine ⟨4294,by decide,by simp [guardState],.jump 4292,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4295 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4295 h x) (guardState ρ 4297 h x) := by
 refine ⟨4295,by decide,by simp [guardState],.jump 4297,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4296_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4296 h 0) (guardState ρ 4302 h 0) := by
 refine ⟨4296,by decide,by simp [guardState],.dec 8 4302 4297,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4296_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4296 h (x+1)) (guardState ρ 4297 h x) := by
 refine ⟨4296,by decide,by simp [guardState],.dec 8 4302 4297,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4296 h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4297:M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ 4296 h (x+1)).registers j) else (guardState ρ 4296 h (x+1)).registers j⟩=some (guardState ρ 4297 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4297_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4297 0 x) (guardState ρ 4299 0 x) := by
 refine ⟨4297,by decide,by simp [guardState],.dec 7 4299 4298,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4297_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4297 (h+1) x) (guardState ρ 4298 h x) := by
 refine ⟨4297,by decide,by simp [guardState],.dec 7 4299 4298,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4297 (h+1) x).registers (registerIndex 7)≠0 from by change h+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4298:M),fun j=>if j.val=7 then modelPredecessor ((guardState ρ 4297 (h+1) x).registers j) else (guardState ρ 4297 (h+1) x).registers j⟩=some (guardState ρ 4298 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4298 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4298 h x) (guardState ρ 4297 h x) := by
 refine ⟨4298,by decide,by simp [guardState],.jump 4297,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4299_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4299 h 0) (guardState ρ 4301 h 0) := by
 refine ⟨4299,by decide,by simp [guardState],.dec 8 4301 4300,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4299_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4299 h (x+1)) (guardState ρ 4300 h x) := by
 refine ⟨4299,by decide,by simp [guardState],.dec 8 4301 4300,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ 4299 h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨(4300:M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ 4299 h (x+1)).registers j) else (guardState ρ 4299 h (x+1)).registers j⟩=some (guardState ρ 4300 h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step4300 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4300 h x) (guardState ρ 4297 h x) := by
 refine ⟨4300,by decide,by simp [guardState],.jump 4297,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4301 (ρ:Nat→M) (h x:M) : programStep (guardState ρ 4301 h x) (guardState ρ 4328 h x) := by
 refine ⟨4301,by decide,by simp [guardState],.jump 4328,by decide,?_⟩
 simp [NativeSource.execute,guardState,registerIndex]

end ZF207.NativeMPCompare
