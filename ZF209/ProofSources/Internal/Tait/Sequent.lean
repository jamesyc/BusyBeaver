module
public import Internal.Tait.Alpha
public import Foundation.FirstOrder.Arithmetic.HFS.PRF
@[expose] public section
/-! # Translation of sequents

A sequent is a finite set `s` of formula codes. Its translation `seqC s m` is
the disjunction of `chiS m p` over `p ∈ s`, in increasing order of `p`, built by
primitive recursion: `disj s m n` collects the members below `n`, and
`seqC s m = disj s m s`. Introduction, elimination and vacuity hold member by
member. -/
namespace ZF209.Internal.Tait
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CKernel.Generic

attribute [local instance] Classical.propDecidable

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The translation of a sequent member: empty bound-label vector, depth `0`,
family `0`, free-label offset `m`. -/
noncomputable def chiS (m q : V) : V := π₁ (tr ⟪0, 0, m, 0⟫ q)

end

noncomputable def chiSDef : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y m q. ∃ par, !pair₄Def par 0 0 m 0 ∧ ∃ t, !(Tr.blueprint.result ℒₛₑₜ) t par q ∧ !pi₁Def y t”

namespace Disj

noncomputable def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “z s m. z = 1”
  succ := .mkSigma “u z n s m. (n ∈ s ∧ ∃ c, !chiSDef c m n ∧ !orDef u c z) ∨ (n ∉ s ∧ u = z)”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma chiS_defined : 𝚺ᴬ₁-Function₂ (chiS : V → V → V) via chiSDef := .mk fun v => by
  simp [chiSDef, chiS, tr_defined.iff]

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 1
  succ v n z := if n ∈ v 0 then cor (chiS (v 1) n) z else z
  zero_defined := .mk fun v => by simp [blueprint]
  succ_defined := .mk fun v => by
    by_cases h : v 2 ∈ v 3 <;> simp [blueprint, h, chiS_defined.iff, cor_defined.iff]

end Disj

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The disjunction of the members of `s` below `n`. -/
noncomputable def disj (s m n : V) : V := Disj.construction.result ![s, m] n

/-- The translation of a sequent. -/
noncomputable def seqC (s m : V) : V := disj s m s

@[simp] lemma disj_zero (s m : V) : disj s m 0 = 1 := by
  simp [disj, Disj.construction]

@[simp] lemma disj_succ (s m n : V) :
    disj s m (n + 1) = if n ∈ s then cor (chiS m n) (disj s m n) else disj s m n := by
  simp [disj, Disj.construction]

instance chiS_definable (Γ m) : Γᴬ_[m + 1]-Function₂ (chiS : V → V → V) :=
  .of_sigmaOne Disj.chiS_defined.to_definable

noncomputable def disjDef : 𝚺ᴬ₁.Semisentence 4 := Disj.blueprint.resultDef

lemma disj_defined : 𝚺ᴬ₁-Function₃ (disj : V → V → V → V) via
    (disjDef.rew (Rew.subst ![#0, #3, #1, #2])) := .mk fun v => by
  have h := (Disj.construction (V := V)).result_defined_iff ![v 0, v 3, v 1, v 2]
  have e : (fun i : Fin 2 => (![v 0, v 3, v 1, v 2] : Fin 4 → V) i.succ.succ) = ![v 1, v 2] := by
    funext i; match i with | 0 => rfl | 1 => rfl
  simp only [disjDef, Bounding.HierarchySymbol.Semiformula.val_rew, Semiformula.eval_rew,
    Function.comp_def]
  simpa [disj, e, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using h

instance disj_definable (Γ m) : Γᴬ_[m + 1]-Function₃ (disj : V → V → V → V) :=
  .of_sigmaOne disj_defined.to_definable

end

/-! ## Introduction, elimination and vacuity -/

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (L : IntLogic V)
open IntLogic Logic

lemma disj_intro (s m : V) : ∀ n : V, ∀ p < n, p ∈ s → L.Pr (imp (chiS m p) (disj s m n)) := by
  refine InductionOnHierarchy.succ_induction_sigma 𝚺 1
    (P := fun n => ∀ p < n, p ∈ s → L.Pr (imp (chiS m p) (disj s m n))) ?_ ?_ ?_
  · definability
  · intro p hp; simp at hp
  · intro n ih p hp hps
    rw [disj_succ]
    rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hp) with hp | rfl
    · have h := ih p hp hps
      split
      · rw [pr_iff] at *
        have c : L.S.toLogic.Ctx [L.S.imp (chiS m p) (disj s m n)] _ :=
          Ctx.deduction (Ctx.orInr (chiS m n) (.mp Ctx.head (Ctx.head.up _)))
        simpa using (c.cut fun b hb => by rw [List.mem_singleton.mp hb]; exact .thm (by simpa using h)).empty
      · exact h
    · rw [if_pos hps, pr_iff]
      simpa using (Ctx.orInl (S := L.S.toLogic) (Γ := [chiS m p]) (disj s m p) Ctx.head).deduction.empty

lemma disj_elim (s m G : V) : ∀ n : V, (∀ p < n, p ∈ s → L.Pr (imp (chiS m p) G)) →
    L.Pr (imp (disj s m n) G) := by
  refine InductionOnHierarchy.succ_induction_sigma 𝚷 2
    (P := fun n => (∀ p < n, p ∈ s → L.Pr (imp (chiS m p) G)) → L.Pr (imp (disj s m n) G))
    ?_ ?_ ?_
  · definability
  · intro _
    rw [disj_zero, pr_iff]
    simpa using L.S.toLogic.explosion G
  · intro n ih h
    have hn := ih (fun p hp hps => h p (lt_trans hp (by simp)) hps)
    rw [disj_succ]
    split
    · rename_i hns
      have hc := h n (by simp) hns
      rw [pr_iff] at *
      have c : L.S.toLogic.Ctx [L.S.or (chiS m n) (disj s m n)] G :=
        Ctx.orElim Ctx.head (.mp Ctx.head (.thm (by simpa using hc)))
          (.mp Ctx.head (.thm (by simpa using hn)))
      simpa using c.deduction.empty
    · exact hn

lemma disj_vac (s m x : V) (hx : x ≠ 0) : ∀ n : V, (∀ p < n, p ∈ s → L.Vac x (chiS m p)) →
    L.Vac x (disj s m n) := by
  refine InductionOnHierarchy.succ_induction_sigma 𝚷 2
    (P := fun n => (∀ p < n, p ∈ s → L.Vac x (chiS m p)) → L.Vac x (disj s m n)) ?_ ?_ ?_
  · simp only [IntLogic.Vac]; definability
  · intro _; rw [disj_zero]; exact vac_bot hx
  · intro n ih h
    have hn := ih (fun p hp hps => h p (lt_trans hp (by simp)) hps)
    rw [disj_succ]
    split
    · rename_i hns
      exact vac_imp (vac_neg (h n (by simp) hns)) hn
    · exact hn

lemma seqC_intro {s m p : V} (hp : p ∈ s) : L.Pr (imp (chiS m p) (seqC s m)) :=
  disj_intro L s m s p (lt_of_mem hp) hp

lemma seqC_elim {s m G : V} (h : ∀ p ∈ s, L.Pr (imp (chiS m p) G)) :
    L.Pr (imp (seqC s m) G) :=
  disj_elim L s m G s (fun p _ hps => h p hps)

lemma seqC_vac {s m x : V} (hx : x ≠ 0) (h : ∀ p ∈ s, L.Vac x (chiS m p)) :
    L.Vac x (seqC s m) :=
  disj_vac L s m x hx s (fun p _ hps => h p hps)

end


section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The translation of a formula without free variables does not depend on the offset. -/
lemma chiS_closed {p : V} (hp : IsUFormula ℒₛₑₜ p) (hs : shift ℒₛₑₜ p = p) :
    ∀ m : V, chiS m p = chiS 0 p := by
  intro m
  induction m using ISigma1.sigma1_succ_induction
  · definability
  · rfl
  · rename_i m ih
    rw [← ih, chiS, chiS, ← tr_shift hp, hs]

end

end ZF209.Internal.Tait
