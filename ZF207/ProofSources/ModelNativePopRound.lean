module
public import ModelNativeUnpairRound
public import ModelNativeTransferGeneric
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativePop
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano M207.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def expected (offset:Nat) : Nat→Instruction
 | 0 => .dec 0 (offset+8) (offset+1)
 | 1 => .inc 5 (offset+2)
 | 2 => .dec 8 (offset+4) (offset+3)
 | 3 => .jump (offset+7)
 | 4 => .dec 5 (offset+7) (offset+5)
 | 5 => .inc 8 (offset+6)
 | 6 => .jump (offset+4)
 | 7 => .jump offset
 | 8 => .dec 5 (offset+11) (offset+9)
 | 9 => .inc 0 (offset+10)
 | _ => .jump (offset+8)
structure Bound (offset:Nat) : Prop where
 range : offset+11<4341
 rows : ∀j:Fin 11,program (offset+j.val)=some (expected offset j.val)
 transfer : NativeTransfer.Bound (offset+4) 5 8
 restore : NativeTransfer.Bound (offset+8) 5 0
noncomputable def unpairState (offset:Nat) (ρ:Nat→M) (pc:Nat) (w h x y:M) : NativeSource.State M :=
 ⟨((offset+pc:Nat):M),![w,ρ 1,ρ 2,ρ 3,ρ 4,y,ρ 6,h,x]⟩
variable {offset:Nat} (hb:Bound offset)
include hb
lemma unpair_step11_zero (ρ:Nat→M) (w h x y:M) : programStep (unpairState offset ρ 0 0 h x y) (unpairState offset ρ 8 0 h x y) := by
 refine ⟨offset+0,by have hh:=hb.range;omega,rfl,.dec 0 (offset+8) (offset+1),by simpa [expected] using hb.rows ⟨0,by decide⟩,?_⟩
 simp [NativeSource.execute,unpairState,registerIndex]
lemma unpair_step11_dec (ρ:Nat→M) (w h x y:M) : programStep (unpairState offset ρ 0 (w+1) h x y) (unpairState offset ρ 1 w h x y) := by
 refine ⟨offset+0,by have hh:=hb.range;omega,rfl,.dec 0 (offset+8) (offset+1),by simpa [expected] using hb.rows ⟨0,by decide⟩,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (unpairState offset ρ 0 (w+1) h x y).registers (registerIndex 0)≠0 from by change w+1≠0; simp)]
 change some ⟨((offset+1:Nat):M),fun j=>if j.val=0 then modelPredecessor ((unpairState offset ρ 0 (w+1) h x y).registers j) else (unpairState offset ρ 0 (w+1) h x y).registers j⟩=some (unpairState offset ρ 1 w h x y)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [unpairState,modelPredecessor_succ]
lemma unpair_step12_inc (ρ:Nat→M) (w h x y:M) : programStep (unpairState offset ρ 1 w h x y) (unpairState offset ρ 2 w h x (y+1)) := by
 refine ⟨offset+1,by have hh:=hb.range;omega,rfl,.inc 5 (offset+2),by simpa [expected] using hb.rows ⟨1,by decide⟩,?_⟩
 simp only [NativeSource.execute,unpairState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [unpairState,modelPredecessor_succ]
lemma unpair_step13_zero (ρ:Nat→M) (w h x y:M) : programStep (unpairState offset ρ 2 w h 0 y) (unpairState offset ρ 4 w h 0 y) := by
 refine ⟨offset+2,by have hh:=hb.range;omega,rfl,.dec 8 (offset+4) (offset+3),by simpa [expected] using hb.rows ⟨2,by decide⟩,?_⟩
 simp [NativeSource.execute,unpairState,registerIndex]
lemma unpair_step13_dec (ρ:Nat→M) (w h x y:M) : programStep (unpairState offset ρ 2 w h (x+1) y) (unpairState offset ρ 3 w h x y) := by
 refine ⟨offset+2,by have hh:=hb.range;omega,rfl,.dec 8 (offset+4) (offset+3),by simpa [expected] using hb.rows ⟨2,by decide⟩,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (unpairState offset ρ 2 w h (x+1) y).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 change some ⟨((offset+3:Nat):M),fun j=>if j.val=8 then modelPredecessor ((unpairState offset ρ 2 w h (x+1) y).registers j) else (unpairState offset ρ 2 w h (x+1) y).registers j⟩=some (unpairState offset ρ 3 w h x y)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [unpairState,modelPredecessor_succ]
lemma unpair_step14_jump (ρ:Nat→M) (w h x y:M) : programStep (unpairState offset ρ 3 w h x y) (unpairState offset ρ 7 w h x y) := by
 refine ⟨offset+3,by have hh:=hb.range;omega,rfl,.jump (offset+7),by simpa [expected] using hb.rows ⟨3,by decide⟩,?_⟩
 simp [NativeSource.execute,unpairState,registerIndex]
lemma unpair_step18_jump (ρ:Nat→M) (w h x y:M) : programStep (unpairState offset ρ 7 w h x y) (unpairState offset ρ 0 w h x y) := by
 refine ⟨offset+7,by have hh:=hb.range;omega,rfl,.jump offset,by simpa [expected] using hb.rows ⟨7,by decide⟩,?_⟩
 simp [NativeSource.execute,unpairState,registerIndex]
lemma unpair_round_positive (ρ:Nat→M) (w h x y:M) :
 nativeReaches (unpairState offset ρ 0 (w+1) h (x+1) y) (unpairState offset ρ 0 w h x (y+1)) := by
 apply nativeReaches_trans (nativeReaches_step (unpair_step11_dec hb ρ w h (x+1) y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step12_inc hb ρ w h (x+1) y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step13_dec hb ρ w h x (y+1)))
 exact nativeReaches_trans (nativeReaches_step (unpair_step14_jump hb ρ w h x (y+1)))
   (nativeReaches_step (unpair_step18_jump hb ρ w h x (y+1)))
lemma unpair_transfer (ρ:Nat→M) (w h x y:M) :
 nativeReaches (unpairState offset ρ 4 w h x y) (unpairState offset ρ 7 w h (x+y) 0) := by
 let frame:Nat→M:=fun i=>if i=0 then w else if i=7 then h else ρ i
 have ht:=NativeTransfer.native_transfer hb.transfer frame y x
 change nativeReaches _ _ at ht
 convert ht using 1
 all_goals
  simp only [unpairState,NativeTransfer.transferState]
  congr 1
  funext j
  rcases j with ⟨j,hj⟩
  have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
  rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [frame]
lemma unpair_round_zero (ρ:Nat→M) (w h y:M) :
 nativeReaches (unpairState offset ρ 0 (w+1) h 0 y) (unpairState offset ρ 0 w h (y+1) 0) := by
 apply nativeReaches_trans (nativeReaches_step (unpair_step11_dec hb ρ w h 0 y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step12_inc hb ρ w h 0 y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step13_zero hb ρ w h 0 (y+1)))
 have ht:=unpair_transfer hb ρ w h 0 (y+1)
 simp only [zero_add] at ht
 exact nativeReaches_trans ht (nativeReaches_step (unpair_step18_jump hb ρ w h (y+1) 0))
end ZF207.NativePop
