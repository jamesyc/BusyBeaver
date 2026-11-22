module
public import ZF192Support.Execution.Registers.Scheduler.FetchSteps
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeCompare
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano RegisterMachine.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- The same ten-row comparison loop occurs at four instruction addresses.
The equality exit is base + 10; the final jump supplies the unequal exit. -/
structure Bound (base unequal : Nat) : Prop where
  range : base + 9 < 4341
  first : program base = some (.dec 7 (base + 4) (base + 1))
  second : program (base + 1) = some (.dec 8 (base + 3) (base + 2))
  repeatCompare : program (base + 2) = some (.jump base)
  startClear : program (base + 3) = some (.jump (base + 5))
  equalOrClear : program (base + 4) = some (.dec 8 (base + 10) (base + 5))
  clearLeft : program (base + 5) = some (.dec 7 (base + 7) (base + 6))
  repeatClearLeft : program (base + 6) = some (.jump (base + 5))
  clearRight : program (base + 7) = some (.dec 8 (base + 9) (base + 8))
  repeatClearRight : program (base + 8) = some (.jump (base + 5))
  exitUnequal : program (base + 9) = some (.jump unequal)

noncomputable def guardState (ρ:Nat→M) (pc h x:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,ρ 1,ρ 2,ρ 3,ρ 4,ρ 5,ρ 6,h,x]⟩
variable {base unequal : Nat} (bound : Bound base unequal)
include bound

lemma step0_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ (base : M) 0 x) (guardState ρ ((base + 4 : Nat) : M) 0 x) := by
 refine ⟨base, by have := bound.range; omega, rfl, .dec 7 (base + 4) (base + 1), bound.first, ?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step0_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ (base : M) (h+1) x) (guardState ρ ((base + 1 : Nat) : M) h x) := by
 refine ⟨base, by have := bound.range; omega, rfl, .dec 7 (base + 4) (base + 1), bound.first, ?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ (base : M) (h+1) x).registers (registerIndex 7)≠0 from by change h+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨((base + 1 : Nat) : M),fun j=>if j.val=7 then modelPredecessor ((guardState ρ (base : M) (h+1) x).registers j) else (guardState ρ (base : M) (h+1) x).registers j⟩=some (guardState ρ ((base + 1 : Nat) : M) h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step1_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 1 : Nat) : M) h 0) (guardState ρ ((base + 3 : Nat) : M) h 0) := by
 refine ⟨(base + 1), by have := bound.range; omega, rfl, .dec 8 (base + 3) (base + 2), bound.second, ?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step1_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 1 : Nat) : M) h (x+1)) (guardState ρ ((base + 2 : Nat) : M) h x) := by
 refine ⟨(base + 1), by have := bound.range; omega, rfl, .dec 8 (base + 3) (base + 2), bound.second, ?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ ((base + 1 : Nat) : M) h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨((base + 2 : Nat) : M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ ((base + 1 : Nat) : M) h (x+1)).registers j) else (guardState ρ ((base + 1 : Nat) : M) h (x+1)).registers j⟩=some (guardState ρ ((base + 2 : Nat) : M) h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step2 (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 2 : Nat) : M) h x) (guardState ρ (base : M) h x) := by
 refine ⟨(base + 2), by have := bound.range; omega, rfl, .jump base, bound.repeatCompare, ?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step3 (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 3 : Nat) : M) h x) (guardState ρ ((base + 5 : Nat) : M) h x) := by
 refine ⟨(base + 3), by have := bound.range; omega, rfl, .jump (base + 5), bound.startClear, ?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 4 : Nat) : M) h 0) (guardState ρ ((base + 10 : Nat) : M) h 0) := by
 refine ⟨(base + 4), by have := bound.range; omega, rfl, .dec 8 (base + 10) (base + 5), bound.equalOrClear, ?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step4_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 4 : Nat) : M) h (x+1)) (guardState ρ ((base + 5 : Nat) : M) h x) := by
 refine ⟨(base + 4), by have := bound.range; omega, rfl, .dec 8 (base + 10) (base + 5), bound.equalOrClear, ?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ ((base + 4 : Nat) : M) h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨((base + 5 : Nat) : M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ ((base + 4 : Nat) : M) h (x+1)).registers j) else (guardState ρ ((base + 4 : Nat) : M) h (x+1)).registers j⟩=some (guardState ρ ((base + 5 : Nat) : M) h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step5_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 5 : Nat) : M) 0 x) (guardState ρ ((base + 7 : Nat) : M) 0 x) := by
 refine ⟨(base + 5), by have := bound.range; omega, rfl, .dec 7 (base + 7) (base + 6), bound.clearLeft, ?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step5_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 5 : Nat) : M) (h+1) x) (guardState ρ ((base + 6 : Nat) : M) h x) := by
 refine ⟨(base + 5), by have := bound.range; omega, rfl, .dec 7 (base + 7) (base + 6), bound.clearLeft, ?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ ((base + 5 : Nat) : M) (h+1) x).registers (registerIndex 7)≠0 from by change h+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨((base + 6 : Nat) : M),fun j=>if j.val=7 then modelPredecessor ((guardState ρ ((base + 5 : Nat) : M) (h+1) x).registers j) else (guardState ρ ((base + 5 : Nat) : M) (h+1) x).registers j⟩=some (guardState ρ ((base + 6 : Nat) : M) h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step6 (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 6 : Nat) : M) h x) (guardState ρ ((base + 5 : Nat) : M) h x) := by
 refine ⟨(base + 6), by have := bound.range; omega, rfl, .jump (base + 5), bound.repeatClearLeft, ?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step7_zero (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 7 : Nat) : M) h 0) (guardState ρ ((base + 9 : Nat) : M) h 0) := by
 refine ⟨(base + 7), by have := bound.range; omega, rfl, .dec 8 (base + 9) (base + 8), bound.clearRight, ?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step7_dec (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 7 : Nat) : M) h (x+1)) (guardState ρ ((base + 8 : Nat) : M) h x) := by
 refine ⟨(base + 7), by have := bound.range; omega, rfl, .dec 8 (base + 9) (base + 8), bound.clearRight, ?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (guardState ρ ((base + 7 : Nat) : M) h (x+1)).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 try simp only [Nat.cast_one,Nat.cast_zero]
 change some ⟨((base + 8 : Nat) : M),fun j=>if j.val=8 then modelPredecessor ((guardState ρ ((base + 7 : Nat) : M) h (x+1)).registers j) else (guardState ρ ((base + 7 : Nat) : M) h (x+1)).registers j⟩=some (guardState ρ ((base + 8 : Nat) : M) h x)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [guardState,modelPredecessor_succ]
lemma step8 (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 8 : Nat) : M) h x) (guardState ρ ((base + 5 : Nat) : M) h x) := by
 refine ⟨(base + 8), by have := bound.range; omega, rfl, .jump (base + 5), bound.repeatClearRight, ?_⟩
 simp [NativeSource.execute,guardState,registerIndex]
lemma step9 (ρ:Nat→M) (h x:M) : programStep (guardState ρ ((base + 9 : Nat) : M) h x) (guardState ρ (unequal : M) h x) := by
 refine ⟨(base + 9), by have := bound.range; omega, rfl, .jump unequal, bound.exitUnequal, ?_⟩
 simp [NativeSource.execute,guardState,registerIndex]

end ZF192Support.NativeCompare
