module
public import CKernel.RestrictedImplication
public import CKernel.Logic
@[expose] public section
/-! # The machine's calculus over an abstract code algebra

The machine's calculus has five code constructors (implication, membership,
equality, universal quantification and the falsity code), the heads 1–6, the
restricted propositional axiom, the pointed gate, modus ponens and
generalization. `Sys X` packages a provability predicate on a type of codes `X`
closed under these rules; `Sys.toLogic` reads it as the portable calculus of
`CKernel.Logic`. `CKernel.Equality` derives the defined equality.

Two instances are used: the standard codes in `ℕ` and the codes of any model of
arithmetic. -/
namespace ZF209.CKernel.Generic

universe u

/-- A provability predicate closed under the machine's rules. -/
structure Sys (X : Type u) extends Codes X where
  Prov : X → Prop
  le : X → X → Prop
  mp {a b : X} : Prov a → Prov (imp a b) → Prov b
  gen (x : X) {a : X} : Prov a → Prov (all x a)
  h1 (d h : X) : Prov (toCodes.head1 d h)
  h2 (d a h : X) : Prov (toCodes.head2 d a h)
  h3 (h d a : X) : Prov (toCodes.head3 h d a)
  h4 (h d a : X) : Prov (toCodes.head4 h d a)
  h5 (d h : X) : Prov (toCodes.head5 d h)
  h6 (d a h : X) : Prov (toCodes.head6 d a h)
  r8 (a b c u : X) : le u a → Prov (toCodes.rho8 a b c u)
  gate (a b c : X) : c ≠ a → c ≠ b → Prov (toCodes.bundle a b c)
  refl (a : X) : le a a
  boundLeft {u a : X} (b : X) : le u a → le u (imp a b)
  boundRight {u b : X} (a : X) : le u b → le u (imp a b)

namespace Sys
variable {X : Type u} (S : Sys X)

local infixr:60 " ⟹ " => S.imp

/-- The restricted propositional basis, read in `S`. -/
def rules : RestrictedImplication.Rules S.imp S.le (fun a => PLift (S.Prov a)) where
  mp := fun h a => ⟨S.mp a.down h.down⟩
  row := fun a b c u h => ⟨S.r8 a b c u h⟩
  refl := S.refl
  boundLeft := S.boundLeft
  boundRight := S.boundRight

theorem k (a b : X) : S.Prov (a ⟹ b ⟹ a) := (RestrictedImplication.k S.rules a b).down
theorem peirce (a b : X) : S.Prov (((a ⟹ b) ⟹ a) ⟹ a) :=
  (RestrictedImplication.peirce S.rules a b).down
theorem s (a b c : X) : S.Prov ((a ⟹ b ⟹ c) ⟹ (a ⟹ b) ⟹ a ⟹ c) :=
  (RestrictedImplication.s S.rules a b c).down
theorem composition (a b c : X) : S.Prov ((a ⟹ b) ⟹ (b ⟹ c) ⟹ a ⟹ c) :=
  (RestrictedImplication.composition S.rules a b c).down
theorem exchange (a b c : X) : S.Prov ((a ⟹ b ⟹ c) ⟹ b ⟹ a ⟹ c) :=
  (RestrictedImplication.exchange S.rules a b c).down

theorem identity (a : X) : S.Prov (a ⟹ a) :=
  S.mp (S.k a a) (S.mp (S.k a (a ⟹ a)) (S.s a (a ⟹ a) a))

/-- Distribution of `∀` over implication. -/
theorem r2 (d a h : X) : S.Prov (S.all d (a ⟹ h) ⟹ S.all d a ⟹ S.all d h) :=
  S.mp (S.h6 d a h) (S.exchange (S.all d a) (S.all d (a ⟹ h)) (S.all d h))

/-- The portable calculus read in `S`. -/
def toLogic : Logic X where
  toCodes := S.toCodes
  Prov := S.Prov
  mp := S.mp
  gen := S.gen
  k := S.k
  s := S.s
  peirce := S.peirce
  r2 := S.r2
  h1 := S.h1
  h2 := S.h2

open Logic in
theorem eqVacuity (a b c : X) (hca : c ≠ a) (hcb : c ≠ b) :
    S.Prov (S.eqVac a b c) := by
  have g : S.toLogic.Ctx [] (S.bundle a b c) := .thm (S.gate a b c hca hcb)
  have hn : S.toLogic.Ctx [S.neg (S.eqVac a b c)] (S.neg (S.eqVac a b c)) := Ctx.head
  have hi : S.toLogic.Ctx [S.neg (S.eqVac a b c)]
      (S.imp (S.eqVac a b c) (S.imp (S.memVac a b c) (S.qGate a b c))) :=
    (Ctx.mp (Ctx.head) (hn.up _) |>.explosion (S.toLogic.imp (S.memVac a b c) (S.qGate a b c))
      |>.deduction)
  exact (Ctx.mp hi (g.up _)).deduction.dne.empty

open Logic in
theorem memVacuity (a b c : X) (hca : c ≠ a) (hcb : c ≠ b) :
    S.Prov (S.memVac a b c) := by
  have g : S.toLogic.Ctx [] (S.bundle a b c) := .thm (S.gate a b c hca hcb)
  have hn : S.toLogic.Ctx [S.neg (S.memVac a b c)] (S.neg (S.memVac a b c)) := Ctx.head
  have hm : S.toLogic.Ctx [S.memVac a b c, S.neg (S.memVac a b c)] (S.qGate a b c) :=
    (Ctx.mp Ctx.head (hn.up _)).explosion _
  have hi : S.toLogic.Ctx [S.neg (S.memVac a b c)]
      (S.imp (S.eqVac a b c) (S.imp (S.memVac a b c) (S.qGate a b c))) :=
    (hm.deduction).lift _
  exact (Ctx.mp hi (g.up _)).deduction.dne.empty

end Sys

end ZF209.CKernel.Generic
