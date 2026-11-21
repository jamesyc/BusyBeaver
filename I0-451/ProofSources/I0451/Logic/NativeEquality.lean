module
public import I0451.Logic.SourceAxiomForms

/-! The native proof calculus proves the equality axioms of the
ordinary set language. These axioms justify using Foundation's
membership-model completeness theorem for the native set theory. -/
@[expose] public section
namespace I0451.Logic

open FFL FFL.Entailment FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.Arithmetization I0451.Omega
open I0451.Logic.NamedFormula ZF207.CKernel.Generic

local notation "K" => calculus.toLogic
local notation "E" => NamedFormula.equal
local notation "N" => NamedFormula.mem

private theorem closed_native_entails {φ : SetTheorySentence} (f : NamedFormula)
    (proof : NativeDerivable f.code)
    (semantics : ∀ (V : Type) [Tarski.Structure ℒₛₑₜ V] [Nonempty V],
      V↓[ℒₛₑₜ] ⊧ f.closedSentence → V↓[ℒₛₑₜ] ⊧ φ) :
    nativeSetTheory ⊢ φ := by
  apply Theory.Proof.complete
  apply consequence_iff.mpr
  intro V _ _ model
  exact semantics V (models_of_provable model (f.closedSentence_provable proof))

private theorem equality_reflexivity : nativeSetTheory ⊢ Theory.Eq.refl ℒₛₑₜ := by
  apply closed_native_entails (E 1 1) (NativeDerivable.native_eq_refl 1)
  intro V _ _ model
  have each := (closedSentence_models (E 1 1)).mp model
  simp [Theory.Eq.refl, models_iff]
  intro x
  exact each (fun _ => x)

private theorem equality_symmetry : nativeSetTheory ⊢ Theory.Eq.symm ℒₛₑₜ := by
  apply closed_native_entails (.imp (E 1 2) (E 2 1)) (NativeDerivable.native_eq_symm 1 2)
  intro V _ _ model
  have each := (closedSentence_models (.imp (E 1 2) (E 2 1))).mp model
  simp [Theory.Eq.symm, models_iff]
  intro x y
  exact each (fun i => if i = 1 then x else y)

private theorem equality_transitivity : nativeSetTheory ⊢ Theory.Eq.trans ℒₛₑₜ := by
  apply closed_native_entails (.imp (E 1 2) (.imp (E 2 3) (E 1 3))) (NativeDerivable.native_eq_trans 1 2 3)
  intro V _ _ model
  have each := (closedSentence_models (.imp (E 1 2) (.imp (E 2 3) (E 1 3)))).mp model
  simp [Theory.Eq.trans, models_iff]
  intro x y z
  exact each (fun i => if i = 1 then x else if i = 2 then y else z)

private theorem relation_ext (r : (ℒₛₑₜ).Rel 2) (atom : Nat → Nat → NamedFormula)
    (atomIs : ∀ (V : Type) [Tarski.Structure ℒₛₑₜ V] (s : Nat → V) (a b : Nat),
      (atom a b).eval s ↔ Tarski.Structure.rel (L := ℒₛₑₜ) r ![s a,s b])
    (proof : NativeDerivable (.imp ((E 1 3).and (E 2 4)) (.imp (atom 1 2) (atom 3 4)) : NamedFormula).code) :
    nativeSetTheory ⊢ Theory.Eq.relExt r := by
  let form : NamedFormula := .imp ((E 1 3).and (E 2 4)) (.imp (atom 1 2) (atom 3 4))
  apply closed_native_entails form proof
  intro V _ _ model
  have each := (closedSentence_models form).mp model
  simp only [Theory.Eq.relExt, models_iff, Semiformula.eval_allClosure]
  intro env
  let s (i : Nat) : V := if i = 1 then env 0 else if i = 2 then env 1 else if i = 3 then env 2 else env 3
  have basic := each s
  have expect₁ : (fun (i : Fin 2) => env (i.addCast 2)) = ![s 1,s 2] := by
    funext i
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl <;> rfl
  have expect₂ : (fun (i : Fin 2) => env (i.addNat 2)) = ![s 3,s 4] := by
    funext i
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl <;> rfl
  change eval s ((E 1 3).and (E 2 4)) → eval s (atom 1 2) → eval s (atom 3 4) at basic
  rw [NamedFormula.eval_and, atomIs V, atomIs V] at basic
  simp [Matrix.conj, Matrix.vecHead, Matrix.vecTail, Semiformula.Operator.val,
    Semiterm.val_bvar, Function.comp_def, expect₁, expect₂, s]
  intro first second holds
  have i0 : Fin.addCast 2 (0 : Fin 2) = (0 : Fin 4) := rfl
  have i1 : Fin.addCast 2 (1 : Fin 2) = (1 : Fin 4) := rfl
  simp only [Semiformula.Operator.Eq.sentence_eq, Semiformula.eval_rel, Function.comp_def,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one, i0, i1,
    Matrix.comp_vecCons', Matrix.vec_single_eq_const] at first second
  have equalitySymbol : (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Language.Set.Rel.eq := rfl
  rw [equalitySymbol] at first second
  apply basic ?_ holds
  constructor
  · simpa [NamedFormula.eval, s, Matrix.vec_single_eq_const] using first
  · simpa [NamedFormula.eval, s, Matrix.vec_single_eq_const] using second

private theorem equality_congruence : nativeSetTheory ⊢ Theory.Eq.relExt Language.Set.Rel.eq := by
  apply relation_ext Language.Set.Rel.eq E (by intro V _ s a b; rfl)
  let hyp := ((E 1 3).and (E 2 4)).code
  let ctx := [(E 1 2).code,hyp]
  have base : (K).Ctx ctx hyp := .hyp (by simp [ctx])
  have h13 := base.andLeft
  have h24 := base.andRight
  have h31 := Logic.Ctx.mp h13 (.thm (NativeDerivable.native_eq_symm (1 : Nat) 3))
  have h12 : (K).Ctx ctx (E 1 2).code := .hyp (by simp [ctx])
  have h32 := h12.mp (h31.mp (.thm (NativeDerivable.native_eq_trans (3 : Nat) 1 2)))
  have h34 := h24.mp (h32.mp (.thm (NativeDerivable.native_eq_trans (3 : Nat) 2 4)))
  exact h34.deduction.deduction.empty

private theorem membership_congruence : nativeSetTheory ⊢ Theory.Eq.relExt Language.Set.Rel.mem := by
  apply relation_ext Language.Set.Rel.mem N (by intro V _ s a b; rfl)
  let hyp := ((E 1 3).and (E 2 4)).code
  let ctx := [(N 1 2).code,hyp]
  have base : (K).Ctx ctx hyp := .hyp (by simp [ctx])
  have atom : (K).Ctx ctx (N 1 2).code := .hyp (by simp [ctx])
  have left := atom.mp (base.andLeft.mp (.thm (NativeDerivable.native_mem_left (1 : Nat) 3 2)))
  have right := left.mp (base.andRight.mp (.thm (NativeDerivable.native_mem_right (2 : Nat) 4 3)))
  exact right.deduction.deduction.empty

instance nativeSetTheory_eq : 𝗘𝗤 ℒₛₑₜ ⪯ nativeSetTheory :=
  Entailment.WeakerThan.ofAxm! fun h => by
    cases h with
    | refl => exact equality_reflexivity
    | symm => exact equality_symmetry
    | trans => exact equality_transitivity
    | funcExt f => exact nomatch f
    | relExt r => cases r
                  · exact equality_congruence
                  · exact membership_congruence

end I0451.Logic
