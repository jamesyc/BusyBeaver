module
public import ModelNativeTransferLoop
public import ModelNativeRestoreYLoop
public import ModelNativeRestoreXLoop
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeSource
open ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def nativeReaches (s t:State M) : Prop := ∀initial hist:M,
 nativeRunHistory initial hist → modelListHead hist=stateCode s →
 ∃out:M,nativeRunHistory initial out ∧ modelListHead out=stateCode t
lemma nativeReaches_step {s t:State M} (h:programStep s t) : nativeReaches s t := by
 intro initial hist hr hh
 refine ⟨modelListCons (stateCode t) hist,?_,modelListHead_cons _ _⟩
 apply nativeRunHistory_extend hr
 rw [hh]; exact ⟨s,t,rfl,rfl,h⟩
lemma nativeReaches_trans {s t u:State M} (a:nativeReaches s t) (b:nativeReaches t u) : nativeReaches s u := by
 intro initial hist hr hh
 obtain ⟨out,ho,he⟩:=a initial hist hr hh
 exact b initial out ho he
noncomputable def unpairState (ρ:Nat→M) (pc w h x y:M) : State M :=
 ⟨pc,![w,ρ 1,ρ 2,ρ 3,ρ 4,y,ρ 6,h,x]⟩
lemma unpair_step11_zero (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 11 0 h x y) (unpairState ρ 19 0 h x y) := by
 refine ⟨11,by decide,by simp [unpairState],.dec 0 19 12,by decide,?_⟩
 simp [execute,unpairState,registerIndex]
lemma unpair_step11_dec (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 11 (w+1) h x y) (unpairState ρ 12 w h x y) := by
 refine ⟨11,by decide,by simp [unpairState],.dec 0 19 12,by decide,?_⟩
 unfold execute
 dsimp only
 rw [if_neg (show (unpairState ρ 11 (w+1) h x y).registers (registerIndex 0)≠0 from by change w+1≠0; simp)]
 change some ⟨(12:M),fun j=>if j.val=0 then modelPredecessor ((unpairState ρ 11 (w+1) h x y).registers j) else (unpairState ρ 11 (w+1) h x y).registers j⟩=some (unpairState ρ 12 w h x y)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [unpairState,modelPredecessor_succ]
lemma unpair_step12_inc (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 12 w h x y) (unpairState ρ 13 w h x (y+1)) := by
 refine ⟨12,by decide,by simp [unpairState],.inc 5 13,by decide,?_⟩
 simp only [execute,unpairState]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [unpairState,modelPredecessor_succ]
lemma unpair_step13_zero (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 13 w h 0 y) (unpairState ρ 15 w h 0 y) := by
 refine ⟨13,by decide,by simp [unpairState],.dec 8 15 14,by decide,?_⟩
 simp [execute,unpairState,registerIndex]
lemma unpair_step13_dec (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 13 w h (x+1) y) (unpairState ρ 14 w h x y) := by
 refine ⟨13,by decide,by simp [unpairState],.dec 8 15 14,by decide,?_⟩
 unfold execute
 dsimp only
 rw [if_neg (show (unpairState ρ 13 w h (x+1) y).registers (registerIndex 8)≠0 from by change x+1≠0; simp)]
 change some ⟨(14:M),fun j=>if j.val=8 then modelPredecessor ((unpairState ρ 13 w h (x+1) y).registers j) else (unpairState ρ 13 w h (x+1) y).registers j⟩=some (unpairState ρ 14 w h x y)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [unpairState,modelPredecessor_succ]
lemma unpair_step14_jump (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 14 w h x y) (unpairState ρ 18 w h x y) := by
 refine ⟨14,by decide,by simp [unpairState],.jump 18,by decide,?_⟩
 simp [execute,unpairState,registerIndex]
lemma unpair_step18_jump (ρ:Nat→M) (w h x y:M) : programStep (unpairState ρ 18 w h x y) (unpairState ρ 11 w h x y) := by
 refine ⟨18,by decide,by simp [unpairState],.jump 11,by decide,?_⟩
 simp [execute,unpairState,registerIndex]
lemma unpair_round_positive (ρ:Nat→M) (w h x y:M) :
 nativeReaches (unpairState ρ 11 (w+1) h (x+1) y) (unpairState ρ 11 w h x (y+1)) := by
 apply nativeReaches_trans (nativeReaches_step (unpair_step11_dec ρ w h (x+1) y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step12_inc ρ w h (x+1) y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step13_dec ρ w h x (y+1)))
 exact nativeReaches_trans (nativeReaches_step (unpair_step14_jump ρ w h x (y+1)))
   (nativeReaches_step (unpair_step18_jump ρ w h x (y+1)))
lemma unpair_transfer (ρ:Nat→M) (w h x y:M) :
 nativeReaches (unpairState ρ 15 w h x y) (unpairState ρ 18 w h (x+y) 0) := by
 let frame:Nat→M:=fun i=>if i=0 then w else if i=7 then h else ρ i
 have ht:=transfer_terminates frame y x
 simpa [transferTerminates,nativeReaches,transferState,unpairState,frame] using ht
lemma unpair_round_zero (ρ:Nat→M) (w h y:M) :
 nativeReaches (unpairState ρ 11 (w+1) h 0 y) (unpairState ρ 11 w h (y+1) 0) := by
 apply nativeReaches_trans (nativeReaches_step (unpair_step11_dec ρ w h 0 y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step12_inc ρ w h 0 y))
 apply nativeReaches_trans (nativeReaches_step (unpair_step13_zero ρ w h 0 (y+1)))
 have ht:=unpair_transfer ρ w h 0 (y+1)
 simp only [zero_add] at ht
 exact nativeReaches_trans ht (nativeReaches_step (unpair_step18_jump ρ w h (y+1) 0))
end ZF209.NativeSource
