module
public import ZF192Support.Execution.Registers.Arithmetic.CopyLoop

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.NativeCopy
open ZF192Support.NativeSource
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

abbrev Bound (base : Nat) := NativeCopyLoop.CopyBound base 3 2 8

noncomputable def drainState (base:Nat) (ρ:Nat→M) (pc:Nat) (n l x:M) : NativeSource.State M :=
 ⟨((base+pc:Nat):M),![ρ 0,ρ 1,l,n,ρ 4,ρ 5,ρ 6,ρ 7,x]⟩

private lemma state_eq (base pc : Nat) (ρ : Nat → M) (n d t : M) :
    NativeCopyLoop.state 3 2 8 ρ ((base+pc:Nat):M) n d t =
      drainState base ρ pc n d t := by
  simp only [NativeCopyLoop.state, drainState, NativeSource.State.mk.injEq, true_and]
  funext i
  rcases i with ⟨i, hi⟩
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases h with h|h|h|h|h|h|h|h|h <;> subst i <;> rfl

theorem native_copy {base : Nat} (hb : Bound base) (ρ : Nat → M) (d t : M) :
    nativeReaches (drainState base ρ 0 d t 0) (drainState base ρ 7 d (t+d) 0) := by
  simpa only [← state_eq, Nat.add_zero] using NativeCopyLoop.native_copy hb ρ d t

lemma bound_4255 : Bound 4255 := by
  constructor <;> constructor <;> decide +kernel

lemma bound_4321 : Bound 4321 := by
  constructor <;> constructor <;> decide +kernel

end ZF192Support.NativeCopy
