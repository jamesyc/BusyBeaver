module
public import ModelNativeFetchLoops
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeFetch
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma fetchPrefix_positive (ρ:Nat→M) (n l:M) : nativeReaches (fetchState ρ 25 n (l+1) 0) (fetchState ρ 34 n l 0) :=
 nativeReaches_trans (nativeReaches_step (fetch_step25_dec ρ n l 0)) (nativeReaches_step (fetch_step26_jump ρ n l 0))
lemma fetchPrefix_fresh (ρ:Nat→M) (n:M) : nativeReaches (fetchState ρ 25 n 0 0) (fetchState ρ 34 (n+1) n 0) := by
 have hd:=drain_terminates ρ n 0 0
 change nativeReaches _ (fetchState ρ 31 0 (0+n) (0+n)) at hd
 rw [zero_add] at hd
 have hr:=restore_terminates ρ n 0 n
 change nativeReaches _ (fetchState ρ 34 (0+n+1) n 0) at hr
 rw [zero_add] at hr
 exact nativeReaches_trans (nativeReaches_step (fetch_step25_zero ρ n 0 0)) (nativeReaches_trans hd hr)
noncomputable def cleanFrame (ρ:Nat→M) : Nat→M := fun i=>if i=4 ∨ i=5 then 0 else ρ i
noncomputable def fetchStart (ρ:Nat→M) (n l:M) := fetchState (cleanFrame ρ) 25 n l 0
noncomputable def fetchSelected (ρ:Nat→M) (n seed:M) : NativeSource.State M :=
 ⟨48,![ρ 0,modelUnpairRight seed,ρ 2,ρ 3,modelUnpairLeft seed,0,n,ρ 7,0]⟩
lemma fetch_decode (ρ:Nat→M) (n seed:M) :
 nativeReaches (fetchState (cleanFrame ρ) 34 n seed 0) (fetchSelected ρ n seed) := by
 let frame:Nat→M:=fun i=>if i=6 then n else cleanFrame ρ i
 have ht:=ResidualSource.native_unpair frame seed
 simpa [ResidualSource.unpairState,fetchSelected,fetchState,frame,cleanFrame] using ht
lemma native_fetch_fresh (ρ:Nat→M) (n:M) : nativeReaches (fetchStart ρ n 0) (fetchSelected ρ (n+1) n) :=
 nativeReaches_trans (fetchPrefix_fresh (cleanFrame ρ) n) (fetch_decode ρ (n+1) n)
lemma native_fetch_positive (ρ:Nat→M) (n l:M) : nativeReaches (fetchStart ρ n (l+1)) (fetchSelected ρ n l) :=
 nativeReaches_trans (fetchPrefix_positive (cleanFrame ρ) n l) (fetch_decode ρ n l)
/-- Native fresh/residual fetch with exact counter update; all retained command registers unchanged. -/
theorem native_fetch (ρ:Nat→M) (n l:M) : nativeReaches (fetchStart ρ n l)
 (fetchSelected ρ (if l=0 then n+1 else n) (if l=0 then n else modelPredecessor l)) := by
 by_cases hl:l=0
 · subst l
   simpa only [ite_true] using native_fetch_fresh ρ n
 · obtain ⟨p,hp⟩:=eq_succ_of_pos (pos_iff_ne_zero.mpr hl)
   subst l
   simpa only [if_neg hl,modelPredecessor_succ] using native_fetch_positive ρ n p
end ZF207.NativeFetch
