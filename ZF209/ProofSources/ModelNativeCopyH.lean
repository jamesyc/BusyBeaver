module
public import ModelNativeCopyHDrain
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeCopyH
open ZF209.NativeSource ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma restore {base:Nat} (hb:Bound base) (ρ:Nat→M) (d t x:M) :
 nativeReaches (drainState base ρ 4 d t x) (drainState base ρ 7 (d+x) t 0) := by
 let frame:Nat→M:=fun i=>if i=2 then t else ρ i
 have ht:=NativeTransfer.native_transfer hb.restore frame x d
 change nativeReaches _ _ at ht
 convert ht using 1
 all_goals
  simp only [drainState,NativeTransfer.transferState]
  congr 1
  funext j
  rcases j with ⟨j,hj⟩
  have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
  rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [frame]
theorem native_copy {base:Nat} (hb:Bound base) (ρ:Nat→M) (d t:M) :
 nativeReaches (drainState base ρ 0 d t 0) (drainState base ρ 7 d (t+d) 0) := by
 have hd:=drain_terminates hb ρ d t 0
 change nativeReaches _ (drainState base ρ 4 0 (t+d) (0+d)) at hd
 rw [zero_add] at hd
 have hr:=restore hb ρ 0 (t+d) d
 rw [zero_add] at hr
 exact nativeReaches_trans hd hr
lemma bound_69 : Bound 69 := by
 constructor <;> try decide
 constructor <;> decide
end ZF209.NativeCopyH
