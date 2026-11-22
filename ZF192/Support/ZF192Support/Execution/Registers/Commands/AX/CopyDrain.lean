module
public import ZF192Support.Execution.Registers.Arithmetic.CopyLoop

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.NativeAXCopy
open ZF192Support.NativeSource
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

abbrev Bound (base : Nat) := NativeCopyLoop.Bound base 4 5 8

noncomputable def drainState (base:Nat) (ρ:Nat→M) (pc:Nat) (n l x:M) : NativeSource.State M :=
 ⟨((base+pc:Nat):M),![ρ 0,ρ 1,ρ 2,ρ 3,n,l,ρ 6,ρ 7,x]⟩

private lemma state_eq (base pc : Nat) (ρ : Nat → M) (n d t : M) :
    NativeCopyLoop.state 4 5 8 ρ ((base+pc:Nat):M) n d t =
      drainState base ρ pc n d t := by
  simp only [NativeCopyLoop.state, drainState, NativeSource.State.mk.injEq, true_and]
  funext i
  rcases i with ⟨i, hi⟩
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases h with h|h|h|h|h|h|h|h|h <;> subst i <;> rfl

def drainTerminates (base : Nat) (ρ : Nat → M) (n : M) : Prop :=
  ∀ d t : M, nativeReaches (drainState base ρ 0 n d t) (drainState base ρ 4 0 (d+n) (t+n))

theorem drain_terminates {base : Nat} (hb : Bound base) (ρ : Nat → M) :
    ∀ n : M, drainTerminates base ρ n := by
  intro n d t
  simpa only [← state_eq, Nat.add_zero] using NativeCopyLoop.drain_terminates hb ρ n d t

end ZF192Support.NativeAXCopy
