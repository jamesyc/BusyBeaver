module
public import ModelNativeTransferGeneric
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeCopy
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
structure Bound (base:Nat) : Prop where
 range : base+7<4341
 row0 : program base=some (.dec 3 (base+4) (base+1))
 row1 : program (base+1)=some (.inc 2 (base+2))
 row2 : program (base+2)=some (.inc 8 (base+3))
 row3 : program (base+3)=some (.jump base)
 restore : NativeTransfer.Bound (base+4) 8 3
noncomputable def drainState (base:Nat) (ρ:Nat→M) (pc:Nat) (n l x:M) : NativeSource.State M :=
 ⟨((base+pc:Nat):M),![ρ 0,ρ 1,l,n,ρ 4,ρ 5,ρ 6,ρ 7,x]⟩
variable {base:Nat} (hb:Bound base)
include hb
lemma drain_step27_zero (ρ:Nat→M) (n l x:M) : programStep (drainState base ρ 0 0 l x) (drainState base ρ 4 0 l x) := by
 refine ⟨base+0,by have hh:=hb.range;omega,rfl,.dec 3 (base+4) (base+1),by simpa only [Nat.add_zero] using hb.row0,?_⟩
 simp [NativeSource.execute,drainState,registerIndex]
lemma drain_step27_dec (ρ:Nat→M) (n l x:M) : programStep (drainState base ρ 0 (n+1) l x) (drainState base ρ 1 n l x) := by
 refine ⟨base+0,by have hh:=hb.range;omega,rfl,.dec 3 (base+4) (base+1),by simpa only [Nat.add_zero] using hb.row0,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (drainState base ρ 0 (n+1) l x).registers (registerIndex 3)≠0 from by change n+1≠0; simp)]
 change some ⟨((base+1:Nat):M),fun j=>if j.val=3 then modelPredecessor ((drainState base ρ 0 (n+1) l x).registers j) else (drainState base ρ 0 (n+1) l x).registers j⟩=some (drainState base ρ 1 n l x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [drainState,modelPredecessor_succ]
lemma drain_step28_inc (ρ:Nat→M) (n l x:M) : programStep (drainState base ρ 1 n l x) (drainState base ρ 2 n (l+1) x) := by
 refine ⟨base+1,by have hh:=hb.range;omega,rfl,.inc 2 (base+2),by simpa only [Nat.add_zero] using hb.row1,?_⟩
 simp only [NativeSource.execute,drainState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [drainState,modelPredecessor_succ]
lemma drain_step29_inc (ρ:Nat→M) (n l x:M) : programStep (drainState base ρ 2 n l x) (drainState base ρ 3 n l (x+1)) := by
 refine ⟨base+2,by have hh:=hb.range;omega,rfl,.inc 8 (base+3),by simpa only [Nat.add_zero] using hb.row2,?_⟩
 simp only [NativeSource.execute,drainState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [drainState,modelPredecessor_succ]
lemma drain_step30_jump (ρ:Nat→M) (n l x:M) : programStep (drainState base ρ 3 n l x) (drainState base ρ 0 n l x) := by
 refine ⟨base+3,by have hh:=hb.range;omega,rfl,.jump base,by simpa only [Nat.add_zero] using hb.row3,?_⟩
 simp [NativeSource.execute,drainState,registerIndex]
end ZF209.NativeCopy
