module
public import ModelResidualUnpair
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeSDrain
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano M207.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def drainState (ρ:Nat→M) (pc n l x:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,ρ 1,l,ρ 3,ρ 4,ρ 5,ρ 6,n,x]⟩
lemma drain_step27_zero (ρ:Nat→M) (n l x:M) : programStep (drainState ρ 4332 0 l x) (drainState ρ 4336 0 l x) := by
 refine ⟨4332,by decide,by simp [drainState],.dec 7 4336 4333,by decide,?_⟩
 simp [NativeSource.execute,drainState,registerIndex]
lemma drain_step27_dec (ρ:Nat→M) (n l x:M) : programStep (drainState ρ 4332 (n+1) l x) (drainState ρ 4333 n l x) := by
 refine ⟨4332,by decide,by simp [drainState],.dec 7 4336 4333,by decide,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (drainState ρ 4332 (n+1) l x).registers (registerIndex 7)≠0 from by change n+1≠0; simp)]
 change some ⟨(4333:M),fun j=>if j.val=7 then modelPredecessor ((drainState ρ 4332 (n+1) l x).registers j) else (drainState ρ 4332 (n+1) l x).registers j⟩=some (drainState ρ 4333 n l x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [drainState,modelPredecessor_succ]
lemma drain_step28_inc (ρ:Nat→M) (n l x:M) : programStep (drainState ρ 4333 n l x) (drainState ρ 4334 n (l+1) x) := by
 refine ⟨4333,by decide,by simp [drainState],.inc 2 4334,by decide,?_⟩
 simp only [NativeSource.execute,drainState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [drainState,modelPredecessor_succ]
lemma drain_step29_inc (ρ:Nat→M) (n l x:M) : programStep (drainState ρ 4334 n l x) (drainState ρ 4335 n l (x+1)) := by
 refine ⟨4334,by decide,by simp [drainState],.inc 8 4335,by decide,?_⟩
 simp only [NativeSource.execute,drainState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [drainState,modelPredecessor_succ]
lemma drain_step30_jump (ρ:Nat→M) (n l x:M) : programStep (drainState ρ 4335 n l x) (drainState ρ 4332 n l x) := by
 refine ⟨4335,by decide,by simp [drainState],.jump 4332,by decide,?_⟩
 simp [NativeSource.execute,drainState,registerIndex]
end ZF207.NativeSDrain
