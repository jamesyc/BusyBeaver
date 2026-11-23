module
public import I3_334Support.Arithmetic.Clock
public import I3_334Support.Machine.Simulation
public import Foundation.FirstOrder.Arithmetic.Definability.Absoluteness
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

@[simp] theorem divIn_nat (a b : Nat) : divIn a b = Nat.div a b := by
  symm
  apply Arithmetic.div_graph.mpr
  constructor
  · intro pos
    refine ⟨Arithmetic.le_def.mpr (Nat.eq_or_lt_of_le (Nat.mul_div_le a b)),?_⟩
    have strict := (Nat.div_lt_iff_lt_mul (x := a) pos).mp (Nat.lt_succ_self (a.div b))
    simpa [Nat.mul_comm] using strict
  · rintro rfl
    exact Nat.div_zero a

private noncomputable def subIn {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b : M) : M := a-b

private theorem subIn_nat (a b : Nat) : subIn a b = Nat.sub a b := by
  symm
  apply Arithmetic.sub_eq_iff.mpr
  constructor
  · intro bound
    have le : b ≤ a := (Arithmetic.le_def.mp bound).elim (fun h => h ▸ Nat.le_refl _) Nat.le_of_lt
    simpa [Nat.add_comm] using (Nat.sub_add_cancel le).symm
  · intro lt
    exact Nat.sub_eq_zero_of_le (Nat.le_of_lt lt)

@[simp] theorem remIn_nat (a b : Nat) : remIn a b = Nat.mod a b := by
  change subIn a (b * divIn a b) = Nat.mod a b
  rw [subIn_nat,divIn_nat,Nat.mul_comm b]
  exact Nat.mod_eq_sub_div_mul.symm

private theorem ofNat_nat (n : Nat) [n.AtLeastTwo] :
    @OfNat.ofNat Nat n (@instOfNatAtLeastTwo Nat n (Arithmetic.natCast Nat) _) = n :=
  Arithmetic.natCast_nat n

theorem digit_nat (table q r : Nat) :
    digit table q r = Nat.mod (table >>> (11 * (2*q+Nat.mod r 2))) 2048 := by
  simp only [digit,divIn_nat,remIn_nat,Arithmetic.natCast_nat,ofNat_nat,
    Arithmetic.exp_nat_eq_two_pow,Nat.shiftRight_eq_div_pow]
  rfl

theorem digit_nat_as_row (m : Machine) (q r : Nat) :
    digit m.packedRows q r = m.row q (Nat.mod r 2) := by
  rw [digit_nat]
  rfl

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem binary_value_cast (φ : 𝚺ᴬ₁.Semisentence 3) (natural : Nat → Nat → Nat) (model : M → M → M)
    (natResult : ∀ a b, φ.val.Evalb ![natural a b,a,b])
    (value : ∀ z a b, φ.val.Evalb ![z,a,b] ↔ z = model a b)
    (a b : Nat) : model (a : M) (b : M) = (natural a b : M) := by
  let v : Fin 3 → Nat := ![natural a b,a,b]
  have cast := sigmaOne_upward_absolute (V := M) φ v (natResult a b)
  have coords : (fun i => ((v i : Nat) : M)) = ![(natural a b : M),(a : M),(b : M)] := by
    funext i
    exact Fin.cases rfl (fun b => Fin.cases rfl (fun c => Fin.cases rfl (fun d => d.elim0) c) b) i
  change φ.val.Evalb (fun i => ((v i : Nat) : M)) at cast
  rw [coords] at cast
  exact ((value _ _ _).mp cast).symm

theorem digit_cast (table q r : Nat) :
    digit (M := M) table (q : M) (r : M) = ((digit (M := Nat) table q r : Nat) : M) :=
  binary_value_cast (rowDef table) (digit table) (digit table)
    (fun a b => (rowDef_eval _ _ _ _).mpr rfl) (rowDef_eval table) q r

theorem divIn_cast (a b : Nat) :
    divIn (M := M) (a : M) (b : M) = ((Nat.div a b : Nat) : M) := by
  apply binary_value_cast (.mkSigma divDef.val (by simp)) Nat.div divIn _ _ a b
  · intro x y
    exact div_defined.iff.mpr (divIn_nat x y).symm
  · exact fun z x y => div_defined.iff

theorem remIn_cast (a b : Nat) :
    remIn (M := M) (a : M) (b : M) = ((Nat.mod a b : Nat) : M) := by
  apply binary_value_cast (.mkSigma remDef.val (by simp)) Nat.mod remIn _ _ a b
  · intro x y
    exact rem_defined.iff.mpr (remIn_nat x y).symm
  · exact fun z x y => rem_defined.iff

theorem digit_at_row (m : Machine) (q : Nat) (tape : M) :
    digit (M := M) m.packedRows (q : M) tape =
      (m.row q (if remIn tape 2 = 1 then 1 else 0) : M) := by
  classical
  rcases mod_two tape with zero | one
  · have h : remIn tape 2 = 0 := zero
    have h' : remIn (0 : M) 2 = 0 := by simp [remIn]
    have same : digit m.packedRows (q : M) tape = digit m.packedRows (q : M) (0 : M) := by
      simp only [digit,h,h']
    rw [same]
    have lifted := digit_cast (M := M) m.packedRows q 0
    have match_ : digit m.packedRows q 0 = m.row q 0 := digit_nat_as_row m q 0
    rw [match_] at lifted
    simpa only [Nat.cast_zero,h,zero_ne_one,↓reduceIte] using lifted
  · have h : remIn tape 2 = 1 := one
    have h' : remIn (1 : M) 2 = 1 := by simp [remIn]
    have same : digit m.packedRows (q : M) tape = digit m.packedRows (q : M) (1 : M) := by
      simp only [digit,h,h']
    rw [same]
    have lifted := digit_cast (M := M) m.packedRows q 1
    have match_ : digit m.packedRows q 1 = m.row q 1 := digit_nat_as_row m q 1
    rw [match_] at lifted
    simpa only [Nat.cast_one,h,↓reduceIte] using lifted

end PalomarI3380.ArithmeticMachine
