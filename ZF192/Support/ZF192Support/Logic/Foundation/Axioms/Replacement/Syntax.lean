module
public import ZF192Support.Logic.Foundation.Axioms.Separation
public import ZF192Support.Logic.Foundation.Axioms.Equality
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

def repOpen (p : SetTheorySemiproposition 2) : Proposition Language.set :=
 “(∀ x, ∃! y, !p x y) → ∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, !p x y”

def swapBinary (i : Nat) := if i=0 then 1 else if i=1 then 0 else i

def totalUnique (phi : Formula) : Formula :=
 .all (.ex (.and (rename swapBinary phi)
   (.all (.imp (rename repBIndex phi) (.eq 0 1)))))

theorem agrees_binary {m : Nat} (ts : Fin 2 → Semiterm Language.set Nat m)
 (sigma : Nat → Nat) (h0 : sigma 0 = termIndex (ts 0))
 (h1 : sigma 1 = termIndex (ts 1)) (hf : ∀ j, sigma (2+j) = m+j) :
 RewAgrees (Rew.subst ts) sigma := by
 intro t
 cases t with
 | bvar i =>
   refine Fin.cases ?_ (fun j => ?_) i
   · simpa [termIndex] using h0.symm
   · have hj : j=0 := Fin.eq_zero j
     subst j; simpa [termIndex] using h1.symm
 | fvar j => simp only [Rew.subst_fvar,termIndex]; exact (hf j).symm
 | func f v => exact Empty.elim f

theorem rep_subst_swap (p : SetTheorySemiproposition 2) :
 toSource (Rewriting.subst p ![(.bvar 1 : Semiterm Language.set Nat 2),.bvar 0]) = rename swapBinary (toSource p) := by
 apply toSource_rew
 apply agrees_binary
 · rfl
 · rfl
 · intro j; simp [swapBinary,show 2+j≠1 by omega]

theorem rep_subst_B (p : SetTheorySemiproposition 2) :
 toSource (Rewriting.subst p ![(.bvar 2 : Semiterm Language.set Nat 3),.bvar 0]) = rename repBIndex (toSource p) := by
 apply toSource_rew
 apply agrees_binary
 · rfl
 · rfl
 · intro j; simp [repBIndex,show 2+j≠1 by omega]; omega

theorem rep_subst_C (p : SetTheorySemiproposition 2) :
 toSource (Rewriting.subst p ![(.bvar 0 : Semiterm Language.set Nat 4),.bvar 1]) = rename repCIndex (toSource p) := by
 apply toSource_rew
 apply agrees_binary
 · rfl
 · rfl
 · intro j; simp [repCIndex,show 2+j≠1 by omega]; omega


def repTotal (p : SetTheorySemiproposition 2) : Proposition Language.set :=
 “∀ x, ∃! y, !p x y”
def repRange (p : SetTheorySemiproposition 2) : Proposition Language.set :=
 “∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, !p x y”

end ZFR.FoundationBridge
