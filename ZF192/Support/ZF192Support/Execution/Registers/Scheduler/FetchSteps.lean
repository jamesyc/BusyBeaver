module
public import ZF192Support.Execution.Registers.Arithmetic.ResidualUnpair
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeFetch
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano RegisterMachine.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def fetchState (ρ:Nat→M) (pc n l x:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,l,ρ 2,ρ 3,ρ 4,ρ 5,n,ρ 7,x]⟩
lemma fetch_step25_zero (ρ:Nat→M) (n l x:M) : programStep (fetchState ρ 25 n 0 x) (fetchState ρ 27 n 0 x) := by
 refine ⟨25,by decide,by simp [fetchState],.dec 1 27 26,by decide,?_⟩
 simp [NativeSource.execute,fetchState,registerIndex]
lemma fetch_step25_dec (ρ:Nat→M) (n l x:M) : programStep (fetchState ρ 25 n (l+1) x) (fetchState ρ 26 n l x) := by
 refine ⟨25,by decide,by simp [fetchState],.dec 1 27 26,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (fetchState ρ 25 n (l+1) x).registers (registerIndex 1)≠0 from by change l+1≠0; simp)]
 change some ⟨(26:M),fun j=>if j.val=1 then modelPredecessor ((fetchState ρ 25 n (l+1) x).registers j) else (fetchState ρ 25 n (l+1) x).registers j⟩=some (fetchState ρ 26 n l x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [fetchState,modelPredecessor_succ]
lemma fetch_step26_jump (ρ:Nat→M) (n l x:M) : programStep (fetchState ρ 26 n l x) (fetchState ρ 34 n l x) := by
 refine ⟨26,by decide,by simp [fetchState],.jump 34,by decide,?_⟩
 simp [NativeSource.execute,fetchState,registerIndex]
lemma fetch_step27_zero (ρ:Nat→M) (n l x:M) : programStep (fetchState ρ 27 0 l x) (fetchState ρ 31 0 l x) := by
 refine ⟨27,by decide,by simp [fetchState],.dec 6 31 28,by decide,?_⟩
 simp [NativeSource.execute,fetchState,registerIndex]
lemma fetch_step27_dec (ρ:Nat→M) (n l x:M) : programStep (fetchState ρ 27 (n+1) l x) (fetchState ρ 28 n l x) := by
 refine ⟨27,by decide,by simp [fetchState],.dec 6 31 28,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (fetchState ρ 27 (n+1) l x).registers (registerIndex 6)≠0 from by change n+1≠0; simp)]
 change some ⟨(28:M),fun j=>if j.val=6 then modelPredecessor ((fetchState ρ 27 (n+1) l x).registers j) else (fetchState ρ 27 (n+1) l x).registers j⟩=some (fetchState ρ 28 n l x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [fetchState,modelPredecessor_succ]
lemma fetch_step28_inc (ρ:Nat→M) (n l x:M) : programStep (fetchState ρ 28 n l x) (fetchState ρ 29 n (l+1) x) := by
 refine ⟨28,by decide,by simp [fetchState],.inc 1 29,by decide,?_⟩
 simp only [NativeSource.execute,fetchState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [fetchState,modelPredecessor_succ]
lemma fetch_step29_inc (ρ:Nat→M) (n l x:M) : programStep (fetchState ρ 29 n l x) (fetchState ρ 30 n l (x+1)) := by
 refine ⟨29,by decide,by simp [fetchState],.inc 8 30,by decide,?_⟩
 simp only [NativeSource.execute,fetchState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [fetchState,modelPredecessor_succ]
lemma fetch_step30_jump (ρ:Nat→M) (n l x:M) : programStep (fetchState ρ 30 n l x) (fetchState ρ 27 n l x) := by
 refine ⟨30,by decide,by simp [fetchState],.jump 27,by decide,?_⟩
 simp [NativeSource.execute,fetchState,registerIndex]
lemma fetch_step31_inc (ρ:Nat→M) (n l x:M) : programStep (fetchState ρ 31 n l x) (fetchState ρ 32 (n+1) l x) := by
 refine ⟨31,by decide,by simp [fetchState],.inc 6 32,by decide,?_⟩
 simp only [NativeSource.execute,fetchState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [fetchState,modelPredecessor_succ]
lemma fetch_step32_zero (ρ:Nat→M) (n l x:M) : programStep (fetchState ρ 32 n l 0) (fetchState ρ 34 n l 0) := by
 refine ⟨32,by decide,by simp [fetchState],.dec 8 34 33,by decide,?_⟩
 simp [NativeSource.execute,fetchState,registerIndex]
lemma fetch_step32_dec (ρ:Nat→M) (n l x:M) : programStep (fetchState ρ 32 n l (x+1)) (fetchState ρ 33 n l x) := by
 refine ⟨32,by decide,by simp [fetchState],.dec 8 34 33,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (fetchState ρ 32 n l (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 change some ⟨(33:M),fun j=>if j.val=8 then modelPredecessor ((fetchState ρ 32 n l (x+1)).registers j) else (fetchState ρ 32 n l (x+1)).registers j⟩=some (fetchState ρ 33 n l x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [fetchState,modelPredecessor_succ]
lemma fetch_step33_jump (ρ:Nat→M) (n l x:M) : programStep (fetchState ρ 33 n l x) (fetchState ρ 31 n l x) := by
 refine ⟨33,by decide,by simp [fetchState],.jump 31,by decide,?_⟩
 simp [NativeSource.execute,fetchState,registerIndex]
end ZF192Support.NativeFetch
