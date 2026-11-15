module
public import ModelNativePairCore
public import ModelNativeTransferGeneric
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativePush
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.NativePair
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
structure Bound (base:Nat) : Prop where
 transferT : NativeTransfer.Bound base 2 8
 transferW : NativeTransfer.Bound (base+3) 0 2
 pair : NativePair.Bound (base+6)
 transferY : NativeTransfer.Bound (base+16) 5 0
lemma drainT {base:Nat} (hb:Bound base) (ρ:Nat→M) (t w x y:M) :
 nativeReaches (pairState base ρ 0 t w x y) (pairState base ρ 3 0 w (x+t) y) := by
 let frame:Nat→M:=fun i=>if i=0 then w else if i=5 then y else ρ i
 have ht:=NativeTransfer.native_transfer hb.transferT frame t x
 change nativeReaches _ _ at ht
 convert ht using 1
 all_goals
  simp only [pairState,NativeTransfer.transferState]
  congr 1
  funext j
  rcases j with ⟨j,hj⟩
  have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
  rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [frame]
lemma drainW {base:Nat} (hb:Bound base) (ρ:Nat→M) (t w x y:M) :
 nativeReaches (pairState base ρ 3 t w x y) (pairState base ρ 6 (t+w) 0 x y) := by
 let frame:Nat→M:=fun i=>if i=8 then x else if i=5 then y else ρ i
 have ht:=NativeTransfer.native_transfer hb.transferW frame w t
 change nativeReaches _ _ at ht
 convert ht using 1
 all_goals
  simp only [pairState,NativeTransfer.transferState]
  congr 1
  funext j
  rcases j with ⟨j,hj⟩
  have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
  rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [frame]
lemma drainY {base:Nat} (hb:Bound base) (ρ:Nat→M) (t w x y:M) :
 nativeReaches (pairState base ρ 16 t w x y) (pairState base ρ 19 t (w+y) x 0) := by
 let frame:Nat→M:=fun i=>if i=2 then t else if i=8 then x else ρ i
 have ht:=NativeTransfer.native_transfer hb.transferY frame y w
 change nativeReaches _ _ at ht
 convert ht using 1
 all_goals
  simp only [pairState,NativeTransfer.transferState]
  congr 1
  funext j
  rcases j with ⟨j,hj⟩
  have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
  rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [frame]
theorem native_push {base:Nat} (hb:Bound base) (ρ:Nat→M) (t w:M) :
 nativeReaches (pairState base ρ 0 t w 0 0) (pairState base ρ 19 0 (modelCantor t w) 0 0) := by
 have h1:=drainT hb ρ t w 0 0
 rw [zero_add] at h1
 have h2:=drainW hb ρ 0 w t 0
 rw [zero_add] at h2
 have h3:=NativePair.native_pair hb.pair ρ w 0 t
 have h3':nativeReaches (pairState base ρ 6 w 0 t 0) (pairState base ρ 16 0 0 0 (modelCantor t w)) := by
  simpa only [pairState,Nat.add_assoc,Nat.reduceAdd,Nat.add_zero] using h3
 have h4:=drainY hb ρ 0 0 0 (modelCantor t w)
 rw [zero_add] at h4
 exact nativeReaches_trans h1 (nativeReaches_trans h2 (nativeReaches_trans h3' h4))
lemma bound_4236 : Bound 4236 := by
 constructor
 · constructor <;> decide
 · constructor <;> decide
 · constructor <;> decide
 · constructor <;> decide
lemma bound_4302 : Bound 4302 := by
 constructor
 · constructor <;> decide
 · constructor <;> decide
 · constructor <;> decide
 · constructor <;> decide
lemma bound_50 : Bound 50 := by
 constructor
 · constructor <;> decide
 · constructor <;> decide
 · constructor <;> decide
 · constructor <;> decide
end ZF209.NativePush
