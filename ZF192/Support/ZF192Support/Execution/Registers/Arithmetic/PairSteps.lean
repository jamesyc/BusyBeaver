module
public import ZF192Support.Execution.Registers.Arithmetic.Footprints
public import ZF192Support.Execution.Registers.Arithmetic.Unpair
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativePair
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano RegisterMachine.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def pairState (offset:Nat) (ρ:Nat→M) (pc:Nat) (t w x y:M) : NativeSource.State M :=
 ⟨((offset+pc:Nat):M),![w,ρ 1,t,ρ 3,ρ 4,y,ρ 6,ρ 7,x]⟩
variable {offset:Nat} (hb:Bound offset)
include hb
lemma pair_step0_zero (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 0 0 w x y) (pairState offset ρ 4 0 w x y) := by
 refine ⟨offset+0,by have hh:=hb.range;omega,rfl,.dec 2 (offset+4) (offset+1),?_,?_⟩
 · simpa [expected] using hb.rows ⟨0,by decide⟩
 · simp [NativeSource.execute,pairState,registerIndex]
lemma pair_step0_dec (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 0 (t+1) w x y) (pairState offset ρ 1 t w x y) := by
 refine ⟨offset+0,by have hh:=hb.range;omega,rfl,.dec 2 (offset+4) (offset+1),?_,?_⟩
 · simpa [expected] using hb.rows ⟨0,by decide⟩
 · unfold NativeSource.execute
   dsimp only
   rw [if_neg (show (pairState offset ρ 0 (t+1) w x y).registers (registerIndex 2)≠0 from by change t+1≠0; simp)]
   change some ⟨((offset+1:Nat):M),fun j=>if j.val=2 then modelPredecessor ((pairState offset ρ 0 (t+1) w x y).registers j) else (pairState offset ρ 0 (t+1) w x y).registers j⟩=some (pairState offset ρ 1 t w x y)
   congr 2
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [pairState,modelPredecessor_succ]
lemma pair_step1_inc (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 1 t w x y) (pairState offset ρ 2 t w x (y+1)) := by
 refine ⟨offset+1,by have hh:=hb.range;omega,rfl,.inc 5 (offset+2),?_,?_⟩
 · simpa [expected] using hb.rows ⟨1,by decide⟩
 · simp only [NativeSource.execute,pairState]
   congr 2
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [pairState,modelPredecessor_succ]
lemma pair_step2_inc (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 2 t w x y) (pairState offset ρ 3 t w (x+1) y) := by
 refine ⟨offset+2,by have hh:=hb.range;omega,rfl,.inc 8 (offset+3),?_,?_⟩
 · simpa [expected] using hb.rows ⟨2,by decide⟩
 · simp only [NativeSource.execute,pairState]
   congr 2
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [pairState,modelPredecessor_succ]
lemma pair_step3_jump (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 3 t w x y) (pairState offset ρ 0 t w x y) := by
 refine ⟨offset+3,by have hh:=hb.range;omega,rfl,.jump (offset+0),?_,?_⟩
 · simpa [expected] using hb.rows ⟨3,by decide⟩
 · simp [NativeSource.execute,pairState,registerIndex]
lemma pair_step4_zero (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 4 t w 0 y) (pairState offset ρ 10 t w 0 y) := by
 refine ⟨offset+4,by have hh:=hb.range;omega,rfl,.dec 8 (offset+10) (offset+5),?_,?_⟩
 · simpa [expected] using hb.rows ⟨4,by decide⟩
 · simp [NativeSource.execute,pairState,registerIndex]
lemma pair_step4_dec (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 4 t w (x+1) y) (pairState offset ρ 5 t w x y) := by
 refine ⟨offset+4,by have hh:=hb.range;omega,rfl,.dec 8 (offset+10) (offset+5),?_,?_⟩
 · simpa [expected] using hb.rows ⟨4,by decide⟩
 · unfold NativeSource.execute
   dsimp only
   rw [if_neg (show (pairState offset ρ 4 t w (x+1) y).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
   change some ⟨((offset+5:Nat):M),fun j=>if j.val=8 then modelPredecessor ((pairState offset ρ 4 t w (x+1) y).registers j) else (pairState offset ρ 4 t w (x+1) y).registers j⟩=some (pairState offset ρ 5 t w x y)
   congr 2
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [pairState,modelPredecessor_succ]
lemma pair_step5_inc (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 5 t w x y) (pairState offset ρ 6 t w x (y+1)) := by
 refine ⟨offset+5,by have hh:=hb.range;omega,rfl,.inc 5 (offset+6),?_,?_⟩
 · simpa [expected] using hb.rows ⟨5,by decide⟩
 · simp only [NativeSource.execute,pairState]
   congr 2
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [pairState,modelPredecessor_succ]
lemma pair_step6_zero (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 6 t w 0 y) (pairState offset ρ 9 t w 0 y) := by
 refine ⟨offset+6,by have hh:=hb.range;omega,rfl,.dec 8 (offset+9) (offset+7),?_,?_⟩
 · simpa [expected] using hb.rows ⟨6,by decide⟩
 · simp [NativeSource.execute,pairState,registerIndex]
lemma pair_step6_dec (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 6 t w (x+1) y) (pairState offset ρ 7 t w x y) := by
 refine ⟨offset+6,by have hh:=hb.range;omega,rfl,.dec 8 (offset+9) (offset+7),?_,?_⟩
 · simpa [expected] using hb.rows ⟨6,by decide⟩
 · unfold NativeSource.execute
   dsimp only
   rw [if_neg (show (pairState offset ρ 6 t w (x+1) y).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
   change some ⟨((offset+7:Nat):M),fun j=>if j.val=8 then modelPredecessor ((pairState offset ρ 6 t w (x+1) y).registers j) else (pairState offset ρ 6 t w (x+1) y).registers j⟩=some (pairState offset ρ 7 t w x y)
   congr 2
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [pairState,modelPredecessor_succ]
lemma pair_step7_inc (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 7 t w x y) (pairState offset ρ 8 (t+1) w x y) := by
 refine ⟨offset+7,by have hh:=hb.range;omega,rfl,.inc 2 (offset+8),?_,?_⟩
 · simpa [expected] using hb.rows ⟨7,by decide⟩
 · simp only [NativeSource.execute,pairState]
   congr 2
   funext j
   rcases j with ⟨j,hj⟩
   have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
   rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [pairState,modelPredecessor_succ]
lemma pair_step8_jump (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 8 t w x y) (pairState offset ρ 6 t w x y) := by
 refine ⟨offset+8,by have hh:=hb.range;omega,rfl,.jump (offset+6),?_,?_⟩
 · simpa [expected] using hb.rows ⟨8,by decide⟩
 · simp [NativeSource.execute,pairState,registerIndex]
lemma pair_step9_jump (ρ:Nat→M) (t w x y:M) : programStep (pairState offset ρ 9 t w x y) (pairState offset ρ 0 t w x y) := by
 refine ⟨offset+9,by have hh:=hb.range;omega,rfl,.jump (offset+0),?_,?_⟩
 · simpa [expected] using hb.rows ⟨9,by decide⟩
 · simp [NativeSource.execute,pairState,registerIndex]
end ZF192Support.NativePair
