module
public import ModelNativePopLoop
public import ModelNativePairCore
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativePop
open ZF209.NativeSource ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma restore {offset:Nat} (hb:Bound offset) (ρ:Nat→M) (w h x y:M) :
 nativeReaches (unpairState offset ρ 8 w h x y) (unpairState offset ρ 11 (w+y) h x 0) := by
 let frame:Nat→M:=fun i=>if i=7 then h else if i=8 then x else ρ i
 have ht:=NativeTransfer.native_transfer hb.restore frame y w
 change nativeReaches _ _ at ht
 convert ht using 1
 all_goals
  simp only [unpairState,NativeTransfer.transferState]
  congr 1
  funext j
  rcases j with ⟨j,hj⟩
  have hh:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
  rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [frame]
theorem native_pop {offset:Nat} (hb:Bound offset) (ρ:Nat→M) (n h:M) :
 nativeReaches (unpairState offset ρ 0 n h 0 0)
 (unpairState offset ρ 11 (modelUnpairRight n) h (modelUnpairLeft n) 0) := by
 have ht:=unpair_loop_terminates hb ρ n h 0 0
 change nativeReaches _ (unpairState offset ρ 8 0 h (modelUnpairLeft (n+modelCantor 0 0)) (modelUnpairRight (n+modelCantor 0 0))) at ht
 rw [modelCantor_zero,add_zero] at ht
 have hr:=restore hb ρ 0 h (modelUnpairLeft n) (modelUnpairRight n)
 rw [zero_add] at hr
 exact nativeReaches_trans ht hr
lemma native_pop_pairState {offset:Nat} (hb:Bound offset) (ρ:Nat→M) (t w:M) :
 nativeReaches (NativePair.pairState offset ρ 0 t w 0 0)
 (NativePair.pairState offset ρ 11 t (modelUnpairRight w) (modelUnpairLeft w) 0) := by
 let frame:Nat→M:=fun i=>if i=2 then t else ρ i
 have ht:=native_pop hb frame w (ρ 7)
 simpa [unpairState,NativePair.pairState,frame] using ht
lemma bound_4262 : Bound 4262 := by
 constructor
 · decide
 · decide
 · constructor <;> decide
 · constructor <;> decide
end ZF209.NativePop
