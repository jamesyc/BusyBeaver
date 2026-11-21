module
public import I3_380.Arithmetic.Numerals
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- Read a fixed-width field of a packed natural number by a model-valued index. -/
def packedFieldDef (packed width range : Nat) : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “v i. ∃ p, !expDef p (↑width*i) ∧ ∃ a, !divDef a ↑packed p ∧ !remDef v a ↑range”

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def packedField (packed width range : Nat) (i : M) : M :=
  remIn (divIn (packed : M) (Exp.exp ((width : M)*i))) (range : M)

theorem packedFieldDef_eval (packed width range : Nat) (v i : M) :
    (packedFieldDef packed width range).val.Evalb ![v,i] ↔ v = packedField packed width range i := by
  simp [packedFieldDef,packedField,remIn,divIn,rem_defined.iff,exp_defined_deltaZero.iff,div_defined.iff,numeral_eq_natCast]

@[definability] instance packedField_definable (packed width range : Nat) :
    𝚺ᴬ₁-Function₁ (packedField (M := M) packed width range) := by
  have graph : 𝚺ᴬ₁-Function₁ (packedField (M := M) packed width range) via
      packedFieldDef packed width range := .mk fun v => by
    rw [Matrix.fun_eq_vec_two v]
    exact packedFieldDef_eval packed width range _ _
  exact graph.to_definable

theorem packedField_cast (packed width range i : Nat) :
    packedField (M := M) packed width range (i : M) =
      (Nat.mod (packed >>> (width*i)) range : M) := by
  let predicate := packedFieldDef packed width range
  have base : predicate.val.Evalb ![Nat.mod (packed >>> (width*i)) range,i] := by
    apply (packedFieldDef_eval packed width range _ _).mpr
    simp only [packedField,divIn_nat,remIn_nat,Arithmetic.natCast_nat,exp_nat_eq_two_pow,Nat.shiftRight_eq_div_pow]
    rfl
  have internal := sigmaOne_upward_absolute (V := M) predicate ![Nat.mod (packed >>> (width*i)) range,i] base
  have coordinates : (Nat.cast ∘ (![Nat.mod (packed >>> (width*i)) range,i] : Fin 2 → Nat)) =
      ![(Nat.mod (packed >>> (width*i)) range : M),(i : M)] := by
    simp [Function.comp_def,Matrix.comp_vecCons',Matrix.constant_eq_singleton]
  rw [coordinates] at internal
  exact ((packedFieldDef_eval packed width range _ _).mp internal).symm

end PalomarI3380.ArithmeticMachine
