module
public import ModelNativeDispatch
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeFetch
open ZF207.NativeSource ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def commandEntry (ρ:Nat→M) (n seed:M) : NativeSource.State M :=
 ⟨dispatchTarget (modelUnpairLeft seed),![ρ 0,modelUnpairRight seed,ρ 2,ρ 3,
 modelPredecessor (modelPredecessor (modelUnpairLeft seed)),0,n,ρ 7,0]⟩
lemma selected_dispatch (ρ:Nat→M) (n seed:M) : nativeReaches (fetchSelected ρ n seed) (commandEntry ρ n seed) := by
 let frame:Nat→M:=fun i=>if i=1 then modelUnpairRight seed else if i=5 then 0 else if i=6 then n else if i=8 then 0 else ρ i
 have ht:=native_dispatch frame (modelUnpairLeft seed)
 simpa [dispatchState,fetchSelected,commandEntry,frame] using ht
/-- Literal native25..49 fetch+dispatch, including fresh-candidate increment. -/
theorem native_fetch_dispatch (ρ:Nat→M) (n l:M) : nativeReaches (fetchStart ρ n l)
 (commandEntry ρ (if l=0 then n+1 else n) (if l=0 then n else modelPredecessor l)) :=
 nativeReaches_trans (native_fetch ρ n l) (selected_dispatch ρ _ _)
end ZF207.NativeFetch
