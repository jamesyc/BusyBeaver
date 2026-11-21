module
public import I0451.Logic.Tait.Derivation

/-! Instantiate the proof translation with the checked native calculus
for the literal machine. -/
@[expose] public section
namespace I0451.Logic.Tait

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Arithmetization

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def nativeLogic : IntLogic V where
  D := nativeDerivableDef
  S := NativeDerivable.equality (fun x => x ≠ rlab 0)
  codes_eq := rfl
  prov_iff f := (nativeDerivable_eval f).symm
  E_eq _ _ := rfl
  ok_iff _ := Iff.rfl
  eq_vacuity _ _ _ := NativeDerivable.native_vac_eq
  mem_sub_left := NativeDerivable.native_mem_left
  mem_sub_right := NativeDerivable.native_mem_right

theorem native_alpha [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] {q : V}
    (shape : IsUFormula ℒₛₑₜ q) (d : V) :
    NativeDerivable (ciff (π₁ (tr ⟪0,0,0,0⟫ q)) (π₁ (tr ⟪0,d,0,1⟫ q))) := by
  let L : IntLogic V := nativeLogic
  have zeroLength : len (0 : V) = 0 := by simp
  have free : EnvFree (0 : V) 0 0 d 1 := by
    intro i inside
    rw [zeroLength] at inside
    exact (not_lt_zero inside).elim
  have labels : EnvNotRes (0 : V) := by
    intro i inside
    rw [zeroLength] at inside
    exact (not_lt_zero inside).elim
  have transports := (tr_alpha L shape 0 0 d 0 0 1 (by simp) free labels).1
  exact (L.pr_iff _).mp transports

end I0451.Logic.Tait
