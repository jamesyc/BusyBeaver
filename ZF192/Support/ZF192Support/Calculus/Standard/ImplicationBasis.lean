module
public import ZF192Support.Calculus.Standard.Derivation
public import ZF192Support.Calculus.Generic.RestrictedImplication
@[expose] public section

/-! Interpret the restricted implication basis in the PA196 source calculus. -/
namespace ZF192Support.CKernel.Dominated
set_option autoImplicit false

abbrev below := Nat.le

def mp (a b : Nat) (major : Derivation (wim a b)) (minor : Derivation a) :
    Derivation b := .mp minor major
def row (a b c u : Nat) (h : u ≤ a) : Derivation (rho8 a b c u) :=
  .r8 a b c u h
theorem refl (a : Nat) : a ≤ a := Nat.le_refl a
theorem le_l {u x : Nat} (y : Nat) (h : u ≤ x) : u ≤ wim x y := by
  have hp := pair_bounds x y
  simp only [wim]
  omega
theorem le_r {u y : Nat} (x : Nat) (h : u ≤ y) : u ≤ wim x y := by
  have hp := pair_bounds x y
  simp only [wim]
  omega

def rules : ZF192Support.CKernel.RestrictedImplication.Rules wim (· ≤ ·) Derivation where
  mp := fun {a b} => mp a b
  row := row
  refl := refl
  boundLeft := le_l
  boundRight := le_r

def rho8_all (a b c u : Nat) :
    Derivation (rho8 a b c u) :=
  ZF192Support.CKernel.RestrictedImplication.rho8All rules a b c u

def composition (a b c : Nat) :
    Derivation (wim (wim a b) (wim (wim b c) (wim a c))) :=
  ZF192Support.CKernel.RestrictedImplication.composition rules a b c

def exchange (a b c : Nat) :
    Derivation (wim (wim a (wim b c)) (wim b (wim a c))) :=
  ZF192Support.CKernel.RestrictedImplication.exchange rules a b c

def k (a b : Nat) :
    Derivation (wim a (wim b a)) :=
  ZF192Support.CKernel.RestrictedImplication.k rules a b

def peirce (a b : Nat) :
    Derivation (wim (wim (wim a b) a) a) :=
  ZF192Support.CKernel.RestrictedImplication.peirce rules a b

def s (a b c : Nat) :
    Derivation (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) :=
  ZF192Support.CKernel.RestrictedImplication.s rules a b c

def lift_right (a b : Nat) (hab : Derivation (wim a b)) (x : Nat) :
    Derivation (wim (wim x a) (wim x b)) :=
  ZF192Support.CKernel.RestrictedImplication.liftRight rules hab x

end ZF192Support.CKernel.Dominated
