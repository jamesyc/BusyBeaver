module
public import ZF192Support.Execution.Registers.Arithmetic.Pop
public import ZF192Support.Execution.Registers.Arithmetic.TimesFour
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeCons
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation ZF192Support.NativePair
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem native_cons {base:Nat} (hp:NativePop.Bound base) (hq:NativePair.Bound (base+11))
 (h4:NativeTimesFour.Bound (base+21)) (ρ:Nat→M) (t w:M) :
 nativeReaches (pairState base ρ 0 t w 0 0)
 (pairState base ρ 27 (4*modelCantor (modelUnpairLeft w) t) (modelUnpairRight w) 0 0) := by
 have a:=NativePop.native_pop_pairState hp ρ t w
 have b:=NativePair.native_pair hq ρ t (modelUnpairRight w) (modelUnpairLeft w)
 have b':nativeReaches (pairState base ρ 11 t (modelUnpairRight w) (modelUnpairLeft w) 0)
  (pairState base ρ 21 0 (modelUnpairRight w) 0 (modelCantor (modelUnpairLeft w) t)) := by
  simpa only [pairState,Nat.add_assoc,Nat.reduceAdd,Nat.add_zero] using b
 have c:=NativeTimesFour.native_times4 h4 ρ (modelCantor (modelUnpairLeft w) t) 0 (modelUnpairRight w) 0
 change nativeReaches _ (pairState (base+21) ρ 6 (0+4*modelCantor (modelUnpairLeft w) t) (modelUnpairRight w) 0 0) at c
 rw [zero_add] at c
 have c':nativeReaches (pairState base ρ 21 0 (modelUnpairRight w) 0 (modelCantor (modelUnpairLeft w) t))
  (pairState base ρ 27 (4*modelCantor (modelUnpairLeft w) t) (modelUnpairRight w) 0 0) := by
  simpa only [pairState,Nat.add_assoc,Nat.reduceAdd,Nat.add_zero] using c
 exact nativeReaches_trans a (nativeReaches_trans b' c')
end ZF192Support.NativeCons
