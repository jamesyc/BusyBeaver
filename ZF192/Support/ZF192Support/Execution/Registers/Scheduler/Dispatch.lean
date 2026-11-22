module
public import ZF192Support.Execution.Registers.Scheduler.Fetch
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeFetch
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation RegisterMachine.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def dispatchState (ρ:Nat→M) (pc a:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,ρ 1,ρ 2,ρ 3,a,ρ 5,ρ 6,ρ 7,ρ 8]⟩
lemma dispatch_zero_step (ρ:Nat→M) (pc z p:Nat) (hb:pc<4341) (hc:program pc=some (.dec 4 z p)) :
 programStep (dispatchState ρ (pc:M) 0) (dispatchState ρ (z:M) 0) := by
 refine ⟨pc,hb,rfl,.dec 4 z p,hc,?_⟩
 simp [NativeSource.execute,dispatchState,registerIndex]
lemma dispatch_positive_step (ρ:Nat→M) (pc z p:Nat) (hb:pc<4341) (hc:program pc=some (.dec 4 z p)) (a:M) :
 programStep (dispatchState ρ (pc:M) (a+1)) (dispatchState ρ (p:M) a) := by
 refine ⟨pc,hb,rfl,.dec 4 z p,hc,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (dispatchState ρ (pc:M) (a+1)).registers (registerIndex 4)≠0 from by change a+1≠0; simp)]
 change some ⟨(p:M),fun j=>if j.val=4 then modelPredecessor ((dispatchState ρ (pc:M) (a+1)).registers j) else (dispatchState ρ (pc:M) (a+1)).registers j⟩=some (dispatchState ρ (p:M) a)
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [dispatchState,modelPredecessor_succ]
lemma dispatch_zero (ρ:Nat→M) : nativeReaches (dispatchState ρ 48 0) (dispatchState ρ 4329 0) :=
 nativeReaches_step (dispatch_zero_step ρ 48 4329 49 (by decide) (by decide))
lemma dispatch_one (ρ:Nat→M) : nativeReaches (dispatchState ρ 48 1) (dispatchState ρ 4222 0) := by
 have h:=dispatch_positive_step ρ 48 4329 49 (by decide) (by decide) 0
 simp only [zero_add] at h
 exact nativeReaches_trans (nativeReaches_step h) (nativeReaches_step (dispatch_zero_step ρ 49 4222 50 (by decide) (by decide)))
lemma dispatch_many (ρ:Nat→M) (a:M) : nativeReaches (dispatchState ρ 48 (a+2)) (dispatchState ρ 50 a) := by
 have h:=nativeReaches_trans (nativeReaches_step (dispatch_positive_step ρ 48 4329 49 (by decide) (by decide) (a+1)))
   (nativeReaches_step (dispatch_positive_step ρ 49 4222 50 (by decide) (by decide) a))
 have he:(a+1)+1=a+2 := by rw [add_assoc]; norm_num
 rw [he] at h
 exact h
noncomputable def dispatchTarget (a:M) : M := if a=0 then 4329 else if a=1 then 4222 else 50
theorem native_dispatch (ρ:Nat→M) (a:M) : nativeReaches (dispatchState ρ 48 a)
 (dispatchState ρ (dispatchTarget a) (modelPredecessor (modelPredecessor a))) := by
 have hp0:modelPredecessor (0:M)=0 := by
   symm; apply (predecessorGraph_value _ _).mp
   exact (predecessorGraph_eval _ _).mpr (Or.inl ⟨rfl,rfl⟩)
 by_cases h0:a=0
 · subst a
   simpa only [dispatchTarget,ite_true,hp0] using dispatch_zero ρ
 · obtain ⟨b,hb⟩:=eq_succ_of_pos (pos_iff_ne_zero.mpr h0)
   subst a
   by_cases hb0:b=0
   · subst b
     have hp1:modelPredecessor (1:M)=0 := by simpa only [zero_add] using modelPredecessor_succ (0:M)
     simpa [dispatchTarget,hp1,hp0] using dispatch_one ρ
   · obtain ⟨c,hc⟩:=eq_succ_of_pos (pos_iff_ne_zero.mpr hb0)
     subst b
     have he:(c+1)+1=c+2 := by rw [add_assoc]; norm_num
     have hn:(c+1)+1≠(1:M) := by
       intro hh
       have h:c+1=0 := add_right_cancel (hh.trans (zero_add (1:M)).symm)
       exact (by simp : c+1≠0) h
     rw [modelPredecessor_succ,modelPredecessor_succ]
     unfold dispatchTarget
     rw [if_neg h0,if_neg hn,he]
     exact dispatch_many ρ c
end ZF192Support.NativeFetch
