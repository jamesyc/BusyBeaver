module
public import I3_380.Calibration.ArithmeticInterpretation.Facts
@[expose] public section
/-! # Quantifier rules at the level of internal theorems

Existential elimination and introduction for internal theories, stated for
theorems (no contexts): `⊢ φ.free → ψ.shift` gives `⊢ ∃φ → ψ`, and
`⊢ φ[t] → ∃φ`. -/
namespace PalomarI3380.Calibration.ArithmeticInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.FFL.FirstOrder.Entailment Entailment.FiniteContext
open FFL.Entailment

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable] {T : InternalTheory V L}

open Classical in
lemma exs_imp! {φ : Semiformula V L 1} {ψ : Formula V L} (h : T ⊢ φ.free 🡒 ψ.shift) :
    T ⊢ ∃¹ φ 🡒 ψ := by
  have h₁ : T ⊢ ∼ψ.shift 🡒 ∼φ.free := contra h
  have h₂ : [∼ψ] ⊢[T] ∀¹ ∼φ := by
    apply TProof.generalize!
    simpa [Bootstrapping.Semiformula.free] using deductInv' h₁
  have h₃ : T ⊢ ∼ψ 🡒 ∀¹ ∼φ := deduct' h₂
  have h₄ : T ⊢ ∼(∀¹ ∼φ) 🡒 ψ := CN_of_CN_left h₃
  simpa using h₄

open Classical in
lemma imp_exs! (φ : Semiformula V L 1) (t : Bootstrapping.Term V L) : T ⊢ φ.subst ![t] 🡒 ∃¹ φ := by
  have h₁ : [∀¹ ∼φ] ⊢[T] (∼φ).subst ![t] := TProof.specialize_with_ctx! by_axm₀ t
  have h₂ : T ⊢ ∀¹ ∼φ 🡒 ∼(φ.subst ![t]) := by simpa using deduct' h₁
  have h₃ : T ⊢ φ.subst ![t] 🡒 ∼(∀¹ ∼φ) := CN_of_CN_right h₂
  simpa using h₃

open Classical in
lemma all_imp! (φ : Semiformula V L 1) (t : Bootstrapping.Term V L) : T ⊢ ∀¹ φ 🡒 φ.subst ![t] :=
  deduct' (TProof.specialize_with_ctx! by_axm₀ t)

open Classical in
lemma imp_all! {C : Formula V L} {φ : Semiformula V L 1} (h : T ⊢ C.shift 🡒 φ.free) :
    T ⊢ C 🡒 ∀¹ φ := by
  apply deduct'
  apply TProof.generalize!
  simpa using deductInv' h

open Classical in
/-- Existential congruence under a side condition. -/
lemma exs_iff_of! {C : Formula V L} {φ ψ : Semiformula V L 1}
    (h : T ⊢ C.shift 🡒 (φ.free 🡘 ψ.free)) : T ⊢ C 🡒 (∃¹ φ 🡘 ∃¹ ψ) := by
  have eψ : T ⊢ ψ.free 🡒 ∃¹ ψ.shift := imp_exs! ψ.shift _
  have eφ : T ⊢ φ.free 🡒 ∃¹ φ.shift := imp_exs! φ.shift _
  have h₁ : T ⊢ φ.free 🡒 (C 🡒 ∃¹ ψ).shift := by
    simp only [Bootstrapping.Semiformula.shift_imp, Bootstrapping.Semiformula.shift_exs]
    exact C_swap (C_trans (C_trans h and₁) (CCC_of_C_right eψ))
  have h₂ : T ⊢ ψ.free 🡒 (C 🡒 ∃¹ φ).shift := by
    simp only [Bootstrapping.Semiformula.shift_imp, Bootstrapping.Semiformula.shift_exs]
    exact C_swap (C_trans (C_trans h and₂) (CCC_of_C_right eφ))
  have k₁ := exs_imp! h₁
  have k₂ := exs_imp! h₂
  exact CK_of_C_of_C (C_swap k₁) (C_swap k₂)

local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := L)

lemma free_exs (φ : Semiformula V L 2) :
    (∃¹ φ).free = ∃¹ (φ.shift.subst ![Bootstrapping.Semiterm.bvar 0, &'0]) := by
  simp [Bootstrapping.Semiformula.free, SemitermVec.q]

lemma free_free₂ (φ : Semiformula V L 2) :
    (φ.shift.subst ![Bootstrapping.Semiterm.bvar 0, &'0]).free = φ.shift.shift.subst ![&'0, &'1] := by
  simp [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs]

lemma exs₂_imp! {φ : Semiformula V L 2} {ψ : Formula V L}
    (h : T ⊢ φ.shift.shift.subst ![&'0, &'1] 🡒 ψ.shift.shift) : T ⊢ ∃¹ ∃¹ φ 🡒 ψ := by
  apply exs_imp!
  rw [free_exs]
  apply exs_imp!
  simpa [free_free₂] using h

lemma imp_exs₂! (φ : Semiformula V L 2) (a b : Bootstrapping.Term V L) : T ⊢ φ.subst ![a, b] 🡒 ∃¹ ∃¹ φ := by
  have h₁ := imp_exs! (T := T) (∃¹ φ) b
  have h₂ := imp_exs! (T := T) (φ.subst ![Bootstrapping.Semiterm.bvar 0, b.bShift]) a
  simp only [Bootstrapping.Semiformula.substs_ex, SemitermVec.q] at h₁
  have e : (φ.subst ![Bootstrapping.Semiterm.bvar 0, b.bShift]).subst ![a] = φ.subst ![a, b] := by
    rw [Bootstrapping.Semiformula.substs_substs]; congr 1; funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [Fin.fin_one_eq_zero j]; simp
  rw [e] at h₂
  have e' : (Bootstrapping.Semiterm.bvar 0 :> Bootstrapping.Semiterm.bShift ⨟ ![b]) =
      ![Bootstrapping.Semiterm.bvar 0, b.bShift] := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rw [Fin.fin_one_eq_zero j]; rfl
  rw [e'] at h₁
  exact C_trans h₂ h₁

lemma all₂_imp! (φ : Semiformula V L 2) (a b : Bootstrapping.Term V L) : T ⊢ ∀¹ ∀¹ φ 🡒 φ.subst ![a, b] := by
  have h₁ := all_imp! (T := T) (∀¹ φ) b
  have h₂ := all_imp! (T := T) (φ.subst ![Bootstrapping.Semiterm.bvar 0, b.bShift]) a
  simp only [Bootstrapping.Semiformula.substs_all, SemitermVec.q] at h₁
  have e : (φ.subst ![Bootstrapping.Semiterm.bvar 0, b.bShift]).subst ![a] = φ.subst ![a, b] := by
    rw [Bootstrapping.Semiformula.substs_substs]; congr 1; funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [Fin.fin_one_eq_zero j]; simp
  rw [e] at h₂
  have e' : (Bootstrapping.Semiterm.bvar 0 :> Bootstrapping.Semiterm.bShift ⨟ ![b]) =
      ![Bootstrapping.Semiterm.bvar 0, b.bShift] := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rw [Fin.fin_one_eq_zero j]; rfl
  rw [e'] at h₁
  exact C_trans h₁ h₂

lemma exs₂_iff_of! {C : Formula V L} {φ ψ : Semiformula V L 2}
    (h : T ⊢ C.shift.shift 🡒 (φ.shift.shift.subst ![&'0, &'1] 🡘 ψ.shift.shift.subst ![&'0, &'1])) :
    T ⊢ C 🡒 (∃¹ ∃¹ φ 🡘 ∃¹ ∃¹ ψ) := by
  apply exs_iff_of!
  rw [free_exs, free_exs]
  apply exs_iff_of!
  simpa [free_free₂] using h

lemma exs_imp_ctx! {C : Formula V L} {φ : Semiformula V L 1} {ψ : Formula V L}
    (h : T ⊢ C.shift 🡒 φ.free 🡒 ψ.shift) : T ⊢ C 🡒 ∃¹ φ 🡒 ψ := by
  have h' : T ⊢ φ.free 🡒 (C 🡒 ψ).shift := by
    simp only [Bootstrapping.Semiformula.shift_imp]
    exact C_swap h
  exact C_swap (exs_imp! h')

lemma exs₂_imp_ctx! {C : Formula V L} {φ : Semiformula V L 2} {ψ : Formula V L}
    (h : T ⊢ C.shift.shift 🡒 φ.shift.shift.subst ![&'0, &'1] 🡒 ψ.shift.shift) :
    T ⊢ C 🡒 ∃¹ ∃¹ φ 🡒 ψ := by
  have h' : T ⊢ φ.shift.shift.subst ![&'0, &'1] 🡒 (C 🡒 ψ).shift.shift := by
    simp only [Bootstrapping.Semiformula.shift_imp]
    exact C_swap h
  exact C_swap (exs₂_imp! h')

lemma imp_exs_of! {C : Formula V L} {φ : Semiformula V L 1} (a : Bootstrapping.Term V L)
    (h : T ⊢ C 🡒 φ.subst ![a]) : T ⊢ C 🡒 ∃¹ φ := by
  exact C_trans h (imp_exs! (T := T) φ a)

lemma imp_exs₂_of! {C : Formula V L} {φ : Semiformula V L 2} (a b : Bootstrapping.Term V L)
    (h : T ⊢ C 🡒 φ.subst ![a, b]) : T ⊢ C 🡒 ∃¹ ∃¹ φ := by
  exact C_trans h (imp_exs₂! (T := T) φ a b)

lemma imp_exs_of₂! {C D : Formula V L} {φ : Semiformula V L 1} (a : Bootstrapping.Term V L)
    (h : T ⊢ C 🡒 D 🡒 φ.subst ![a]) : T ⊢ C 🡒 D 🡒 ∃¹ φ := by
  exact C_trans h (CCC_of_C_right (imp_exs! (T := T) φ a))

lemma imp_exs₂_of₂! {C D : Formula V L} {φ : Semiformula V L 2} (a b : Bootstrapping.Term V L)
    (h : T ⊢ C 🡒 D 🡒 φ.subst ![a, b]) : T ⊢ C 🡒 D 🡒 ∃¹ ∃¹ φ := by
  exact C_trans h (CCC_of_C_right (imp_exs₂! (T := T) φ a b))

lemma imp_exs_of₃! {C D E : Formula V L} {φ : Semiformula V L 1} (a : Bootstrapping.Term V L)
    (h : T ⊢ C 🡒 D 🡒 E 🡒 φ.subst ![a]) : T ⊢ C 🡒 D 🡒 E 🡒 ∃¹ φ := by
  exact C_trans h (CCC_of_C_right (CCC_of_C_right (imp_exs! (T := T) φ a)))

lemma imp_exs₂_of₃! {C D E : Formula V L} {φ : Semiformula V L 2} (a b : Bootstrapping.Term V L)
    (h : T ⊢ C 🡒 D 🡒 E 🡒 φ.subst ![a, b]) : T ⊢ C 🡒 D 🡒 E 🡒 ∃¹ ∃¹ φ := by
  exact C_trans h (CCC_of_C_right (CCC_of_C_right (imp_exs₂! (T := T) φ a b)))

end PalomarI3380.Calibration.ArithmeticInterpretation
