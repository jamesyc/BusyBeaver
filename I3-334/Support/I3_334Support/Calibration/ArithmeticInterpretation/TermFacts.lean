module
public import I3_334Support.Calibration.ArithmeticInterpretation.TypedEq
@[expose] public section
/-! # Graphs of terms are functional, congruent and total

For every internal ℒₒᵣ term `t` without bound variables, `U` proves that the
graph of `t` is functional and closed under the equality template, and that
it has a value. Each is a Σ1 induction on `t`. -/
namespace PalomarI3380.Calibration.ArithmeticInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.FFL.FirstOrder.Entailment

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := GraphLanguage)
local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := GraphLanguage)

/-- Induction over typed ℒₒᵣ terms for a Σ1 family of provable codes. -/
theorem term_ind {n : ℕ} (U : Theory GraphLanguage) [U.Δ₁] (C : V → V) (hC : 𝚺ᴬ₁-Function₁ C)
    (hbvar : ∀ z : Fin n, Bootstrapping.Provable U (C (Bootstrapping.Semiterm.bvar z :
      Bootstrapping.Semiterm V ℒₒᵣ n).val))
    (hfvar : ∀ x : V, Bootstrapping.Provable U (C (Bootstrapping.Semiterm.fvar x :
      Bootstrapping.Semiterm V ℒₒᵣ n).val))
    (hzero : Bootstrapping.Provable U (C (𝕹 0 : Bootstrapping.Semiterm V ℒₒᵣ n).val))
    (hone : Bootstrapping.Provable U (C (𝕹 1 : Bootstrapping.Semiterm V ℒₒᵣ n).val))
    (hadd : ∀ a b : Bootstrapping.Semiterm V ℒₒᵣ n, Bootstrapping.Provable U (C a.val) →
      Bootstrapping.Provable U (C b.val) → Bootstrapping.Provable U (C (a + b).val))
    (hmul : ∀ a b : Bootstrapping.Semiterm V ℒₒᵣ n, Bootstrapping.Provable U (C a.val) →
      Bootstrapping.Provable U (C b.val) → Bootstrapping.Provable U (C (a * b).val))
    (t : Bootstrapping.Semiterm V ℒₒᵣ n) : Bootstrapping.Provable U (C t.val) := by
  have hP : 𝚺ᴬ₁-Predicate (fun x : V => Bootstrapping.Provable U (C x)) := by
    haveI := hC; definability
  refine IsSemiterm.sigma1_induction (P := fun x => Bootstrapping.Provable U (C x)) hP ?_ ?_ ?_
    t.val t.isSemiterm
  · intro z hz
    rcases eq_fin_of_lt_nat hz with ⟨i, rfl⟩
    simpa using hbvar i
  · intro x; simpa using hfvar x
  · intro k f v hf hv ih
    rcases lor_func_cases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : v = 0 := by simpa using hv
      subst this
      simpa [qqZero_eq_qqFunc] using hzero
    · have : v = 0 := by simpa using hv
      subst this
      simpa [qqOne_eq_qqFunc] using hone
    · let a : Bootstrapping.Semiterm V ℒₒᵣ n := ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let b : Bootstrapping.Semiterm V ℒₒᵣ n := ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have e : (^func (2 : V) (addIndex : V) v : V) = (a + b).val := by
        simp [a, b, qqAdd, vec2_eq' hv.lh]
      rw [e]; exact hadd a b (ih 0 (by simp)) (ih 1 (by simp))
    · let a : Bootstrapping.Semiterm V ℒₒᵣ n := ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let b : Bootstrapping.Semiterm V ℒₒᵣ n := ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have e : (^func (2 : V) (mulIndex : V) v : V) = (a * b).val := by
        simp [a, b, qqMul, vec2_eq' hv.lh]
      rw [e]; exact hmul a b (ih 0 (by simp)) (ih 1 (by simp))

lemma num3 : (2 : V) + 1 = 3 := by norm_num
lemma num4 : (3 : V) + 1 = 4 := by norm_num
lemma num5 : (4 : V) + 1 = 5 := by norm_num
lemma num6 : (5 : V) + 1 = 6 := by norm_num
lemma num7 : (6 : V) + 1 = 7 := by norm_num
lemma num8 : (7 : V) + 1 = 8 := by norm_num

/-- Normal form for typed `GraphLanguage` formulas built from graphs. -/
macro "nrm" : tactic => `(tactic| simp [SemitermVec.q, Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiterm.shift_substs,
  Bootstrapping.Semiformula.substs_substs, gr_add, gr_mul, gr_subst₂, one_add_one_eq_two, num3, num4, num5,
  num6, num7, num8])
macro "nrm" " at" h:(ppSpace colGt ident)+ : tactic => `(tactic| simp [SemitermVec.q,
  Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiterm.shift_substs, Bootstrapping.Semiformula.substs_substs, gr_add, gr_mul, gr_subst₂,
  one_add_one_eq_two, num3, num4, num5, num6, num7, num8] at $h*)

variable (ι : Interp)

/-! ## Statements -/

noncomputable def funC (e t : V) : V :=
  ^∀ ^∀ imp GraphLanguage (subst GraphLanguage (^#1 ∷ 0) (G ι e 0 t))
    (imp GraphLanguage (subst GraphLanguage (^#0 ∷ 0) (G ι e 0 t)) (subst GraphLanguage (e ∷ ^#1 ∷ ^#0 ∷ 0) (tq ι.eq : V)))

noncomputable def congC (e t : V) : V :=
  ^∀ ^∀ imp GraphLanguage (subst GraphLanguage (e ∷ ^#1 ∷ ^#0 ∷ 0) (tq ι.eq : V))
    (imp GraphLanguage (subst GraphLanguage (^#1 ∷ 0) (G ι e 0 t)) (subst GraphLanguage (^#0 ∷ 0) (G ι e 0 t)))

noncomputable def totC (e t : V) : V := ^∃ G ι e 0 t

instance funC_definable : 𝚺ᴬ₁-Function₂ (funC ι : V → V → V) := by unfold funC; definability
instance congC_definable : 𝚺ᴬ₁-Function₂ (congC ι : V → V → V) := by unfold congC; definability
instance totC_definable : 𝚺ᴬ₁-Function₂ (totC ι : V → V → V) := by unfold totC; definability

/-- The equality template at the marker and two terms. -/
noncomputable abbrev tEq {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) (a b : Bootstrapping.Semiterm V GraphLanguage n) :
    Bootstrapping.Semiformula V GraphLanguage n :=
  (⌜ι.eq⌝ : Bootstrapping.Semiformula V GraphLanguage 3).subst ![cl e, a, b]

variable (e : Bootstrapping.Term V GraphLanguage)

noncomputable def funF (t : Bootstrapping.Term V ℒₒᵣ) : Bootstrapping.Formula V GraphLanguage :=
  ∀¹ ∀¹ ((gr ι e t).subst ![#'1] 🡒 (gr ι e t).subst ![#'0] 🡒 tEq ι e #'1 #'0)

noncomputable def congF (t : Bootstrapping.Term V ℒₒᵣ) : Bootstrapping.Formula V GraphLanguage :=
  ∀¹ ∀¹ (tEq ι e #'1 #'0 🡒 (gr ι e t).subst ![#'1] 🡒 (gr ι e t).subst ![#'0])

noncomputable def totF (t : Bootstrapping.Term V ℒₒᵣ) : Bootstrapping.Formula V GraphLanguage := ∃¹ gr ι e t

lemma funF_val (t : Bootstrapping.Term V ℒₒᵣ) : (funF ι e t).val = funC ι e.val t.val := by
  simp [funF, funC, tmpl_val]
lemma congF_val (t : Bootstrapping.Term V ℒₒᵣ) : (congF ι e t).val = congC ι e.val t.val := by
  simp [congF, congC, tmpl_val]
lemma totF_val (t : Bootstrapping.Term V ℒₒᵣ) : (totF ι e t).val = totC ι e.val t.val := by
  simp [totF, totC]

@[simp] lemma funF_shift (t : Bootstrapping.Term V ℒₒᵣ) :
    (funF ι e t).shift = funF ι e.shift t.shift := by
  simp [funF, Bootstrapping.Semiformula.shift_substs]
@[simp] lemma congF_shift (t : Bootstrapping.Term V ℒₒᵣ) :
    (congF ι e t).shift = congF ι e.shift t.shift := by
  simp [congF, Bootstrapping.Semiformula.shift_substs]
@[simp] lemma totF_shift (t : Bootstrapping.Term V ℒₒᵣ) :
    (totF ι e t).shift = totF ι e.shift t.shift := by
  simp [totF]

/-- The propositional skeleton of functionality for a binary operation. -/
lemma prop_fun {L : Language} [L.Encodable] [L.LORDefinable] {T : InternalTheory V L}
    {a₃ a₁ b₂ b₀ e₃₁ e₂₀ x y z w e : Bootstrapping.Formula V L}
    (ia : T ⊢ a₃ 🡒 a₁ 🡒 e₃₁) (ib : T ⊢ b₂ 🡒 b₀ 🡒 e₂₀) (c₁ : T ⊢ e₃₁ 🡒 x 🡒 y)
    (c₂ : T ⊢ e₂₀ 🡒 y 🡒 z) (f : T ⊢ z 🡒 w 🡒 e) :
    T ⊢ (a₃ ⋏ b₂) ⋏ x 🡒 (a₁ ⋏ b₀) ⋏ w 🡒 e := by
  classical
  apply Entailment.FiniteContext.deduct'
  apply Entailment.FiniteContext.deduct
  have hP : [(a₁ ⋏ b₀) ⋏ w, (a₃ ⋏ b₂) ⋏ x] ⊢[T] (a₁ ⋏ b₀) ⋏ w := Entailment.FiniteContext.by_axm₀
  have hQ : [(a₁ ⋏ b₀) ⋏ w, (a₃ ⋏ b₂) ⋏ x] ⊢[T] (a₃ ⋏ b₂) ⋏ x :=
    Entailment.FiniteContext.by_axm (by simp)
  have ha₁ := Entailment.K_left (Entailment.K_left hP)
  have hb₀ := Entailment.K_right (Entailment.K_left hP)
  have hw := Entailment.K_right hP
  have ha₃ := Entailment.K_left (Entailment.K_left hQ)
  have hb₂ := Entailment.K_right (Entailment.K_left hQ)
  have hx := Entailment.K_right hQ
  have he₃₁ := Entailment.FiniteContext.of' ia ⨀ ha₃ ⨀ ha₁
  have he₂₀ := Entailment.FiniteContext.of' ib ⨀ hb₂ ⨀ hb₀
  have hy := Entailment.FiniteContext.of' c₁ ⨀ he₃₁ ⨀ hx
  have hz := Entailment.FiniteContext.of' c₂ ⨀ he₂₀ ⨀ hy
  exact Entailment.FiniteContext.of' f ⨀ hz ⨀ hw

/-! ## Proofs -/

variable {ι e} {U : Theory GraphLanguage} [U.Δ₁]

theorem tcong (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage) (t : Bootstrapping.Term V ℒₒᵣ) :
    U.internalize V ⊢ congF ι e t := by
  apply tprovable_iff_provable.mpr
  rw [congF_val]
  refine term_ind U (congC ι e.val) (by definability) (fun z => z.elim0) ?_ ?_ ?_ ?_ ?_ t
  · intro x
    rw [← congF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    have s := tE_symm hF (e.shift.shift) (&'1) (&'0)
    have tr := tE_trans hF (e.shift.shift) (&'0) (&'1) (&'(x + 1 + 1))
    simp only [tE] at s tr
    exact Entailment.C_trans s tr
  · rw [← congF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    have c := tZ_cong hF (e.shift.shift) (&'1) (&'0)
    simp only [tE, tZ] at c
    exact c
  · rw [← congF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    have c := tO_cong hF (e.shift.shift) (&'1) (&'0)
    simp only [tE, tO] at c
    exact c
  · intro a b _ _
    rw [← congF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    apply exs₂_imp_ctx!
    nrm
    refine imp_exs₂_of₂! (&'0) (&'1) ?_
    nrm
    have c := tA_cong₃ hF (e.shift.shift.shift.shift) (&'1) (&'0) (&'3) (&'2)
    simp only [tE, tA] at c
    cl_prover [c]
  · intro a b _ _
    rw [← congF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    apply exs₂_imp_ctx!
    nrm
    refine imp_exs₂_of₂! (&'0) (&'1) ?_
    nrm
    have c := tM_cong₃ hF (e.shift.shift.shift.shift) (&'1) (&'0) (&'3) (&'2)
    simp only [tE, tM] at c
    cl_prover [c]

theorem tfun (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage) (t : Bootstrapping.Term V ℒₒᵣ) :
    U.internalize V ⊢ funF ι e t := by
  apply tprovable_iff_provable.mpr
  rw [funF_val]
  refine term_ind U (funC ι e.val) (by definability) (fun z => z.elim0) ?_ ?_ ?_ ?_ ?_ t
  · intro x
    rw [← funF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    have s := tE_symm hF (e.shift.shift) (&'0) (&'(x + 1 + 1))
    have tr := tE_trans hF (e.shift.shift) (&'1) (&'(x + 1 + 1)) (&'0)
    simp only [tE] at s tr
    exact Entailment.C_trans tr (Entailment.CCC_of_C_left s)
  · rw [← funF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    have c := tZ_fun hF (e.shift.shift) (&'1) (&'0)
    simp only [tE, tZ] at c
    exact c
  · rw [← funF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    have c := tO_fun hF (e.shift.shift) (&'1) (&'0)
    simp only [tE, tO] at c
    exact c
  · intro a b iha ihb
    have ia : U.internalize V ⊢ funF ι e a := tprovable_iff_provable.mpr (by rwa [funF_val])
    have ib : U.internalize V ⊢ funF ι e b := tprovable_iff_provable.mpr (by rwa [funF_val])
    rw [← funF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    apply exs₂_imp!
    nrm
    apply exs₂_imp_ctx!
    nrm
    have ia6 := TProof.shift! (TProof.shift! (TProof.shift! (TProof.shift! (TProof.shift!
      (TProof.shift! ia)))))
    have ib6 := TProof.shift! (TProof.shift! (TProof.shift! (TProof.shift! (TProof.shift!
      (TProof.shift! ib)))))
    simp only [funF_shift] at ia6 ib6
    unfold funF at ia6 ib6
    have ia' := all₂_imp! _ (&'1) (&'3) ⨀ ia6
    have ib' := all₂_imp! _ (&'0) (&'2) ⨀ ib6
    nrm at ia' ib'
    have c₁ := tA_cong₁ hF (e.shift.shift.shift.shift.shift.shift) (&'3) (&'1) (&'2) (&'5)
    have c₂ := tA_cong₂ hF (e.shift.shift.shift.shift.shift.shift) (&'1) (&'2) (&'0) (&'5)
    have f := tA_fun hF (e.shift.shift.shift.shift.shift.shift) (&'1) (&'0) (&'5) (&'4)
    simp only [tE, tA] at c₁ c₂ f
    exact prop_fun ia' ib' c₁ c₂ f
  · intro a b iha ihb
    have ia : U.internalize V ⊢ funF ι e a := tprovable_iff_provable.mpr (by rwa [funF_val])
    have ib : U.internalize V ⊢ funF ι e b := tprovable_iff_provable.mpr (by rwa [funF_val])
    rw [← funF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    apply exs₂_imp!
    nrm
    apply exs₂_imp_ctx!
    nrm
    have ia6 := TProof.shift! (TProof.shift! (TProof.shift! (TProof.shift! (TProof.shift!
      (TProof.shift! ia)))))
    have ib6 := TProof.shift! (TProof.shift! (TProof.shift! (TProof.shift! (TProof.shift!
      (TProof.shift! ib)))))
    simp only [funF_shift] at ia6 ib6
    unfold funF at ia6 ib6
    have ia' := all₂_imp! _ (&'1) (&'3) ⨀ ia6
    have ib' := all₂_imp! _ (&'0) (&'2) ⨀ ib6
    nrm at ia' ib'
    have c₁ := tM_cong₁ hF (e.shift.shift.shift.shift.shift.shift) (&'3) (&'1) (&'2) (&'5)
    have c₂ := tM_cong₂ hF (e.shift.shift.shift.shift.shift.shift) (&'1) (&'2) (&'0) (&'5)
    have f := tM_fun hF (e.shift.shift.shift.shift.shift.shift) (&'1) (&'0) (&'5) (&'4)
    simp only [tE, tM] at c₁ c₂ f
    exact prop_fun ia' ib' c₁ c₂ f

lemma tZ_ex (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage) :
    U.internalize V ⊢ ∃¹ (⌜ι.zero⌝ : Bootstrapping.Semiformula V GraphLanguage 2).subst ![cl e, #'0] := by
  have h := TProof.specialize! (by simpa using internal_provable_of_outer_provable (V := V) hF.zero_ex) e
  simpa [Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb, SemitermVec.q,
    Semiformula.substs_substs, Bootstrapping.Semiformula.substs_substs, Matrix.vecHead,
    Matrix.vecTail] using h

lemma tO_ex (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage) :
    U.internalize V ⊢ ∃¹ (⌜ι.one⌝ : Bootstrapping.Semiformula V GraphLanguage 2).subst ![cl e, #'0] := by
  have h := TProof.specialize! (by simpa using internal_provable_of_outer_provable (V := V) hF.one_ex) e
  simpa [Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb, SemitermVec.q,
    Semiformula.substs_substs, Bootstrapping.Semiformula.substs_substs, Matrix.vecHead,
    Matrix.vecTail] using h

lemma tA_ex (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage) (a b : V) :
    U.internalize V ⊢
      ∃¹ (⌜ι.add⌝ : Bootstrapping.Semiformula V GraphLanguage 4).subst ![cl e, &'a, &'b, #'0] := by
  have h := TProof.specialize₃! (by simpa using internal_provable_of_outer_provable (V := V) hF.add_ex)
    (&'b) (&'a) e
  simpa [Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb, SemitermVec.q,
    Semiformula.substs_substs, Bootstrapping.Semiformula.substs_substs, Matrix.vecHead,
    Matrix.vecTail] using h

lemma tM_ex (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage) (a b : V) :
    U.internalize V ⊢
      ∃¹ (⌜ι.mul⌝ : Bootstrapping.Semiformula V GraphLanguage 4).subst ![cl e, &'a, &'b, #'0] := by
  have h := TProof.specialize₃! (by simpa using internal_provable_of_outer_provable (V := V) hF.mul_ex)
    (&'b) (&'a) e
  simpa [Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb, SemitermVec.q,
    Semiformula.substs_substs, Bootstrapping.Semiformula.substs_substs, Matrix.vecHead,
    Matrix.vecTail] using h

theorem ttot (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage) (t : Bootstrapping.Term V ℒₒᵣ) :
    U.internalize V ⊢ totF ι e t := by
  apply tprovable_iff_provable.mpr
  rw [totF_val]
  refine term_ind U (totC ι e.val) (by definability) (fun z => z.elim0) ?_ ?_ ?_ ?_ ?_ t
  · intro x
    rw [← totF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.exs! (&'x)
    nrm
    simpa [tE] using tE_refl hF e (&'x)
  · rw [← totF_val ι e]; apply tprovable_iff_provable.mp
    simpa [totF] using tZ_ex hF e
  · rw [← totF_val ι e]; apply tprovable_iff_provable.mp
    simpa [totF] using tO_ex hF e
  · intro a b iha ihb
    have ia : U.internalize V ⊢ totF ι e a := tprovable_iff_provable.mpr (by rwa [totF_val])
    have ib : U.internalize V ⊢ totF ι e b := tprovable_iff_provable.mpr (by rwa [totF_val])
    rw [← totF_val ι e]; apply tprovable_iff_provable.mp
    unfold totF at ia ib ⊢
    refine ?_ ⨀ ia ⨀ ib
    apply exs_imp!
    nrm
    apply exs_imp_ctx!
    nrm
    refine ?_ ⨀ tA_ex hF (e.shift.shift) 1 0
    apply exs_imp!
    nrm
    refine imp_exs_of₃! (&'0) ?_
    nrm
    refine imp_exs₂_of₃! (&'1) (&'2) ?_
    nrm
    cl_prover
  · intro a b iha ihb
    have ia : U.internalize V ⊢ totF ι e a := tprovable_iff_provable.mpr (by rwa [totF_val])
    have ib : U.internalize V ⊢ totF ι e b := tprovable_iff_provable.mpr (by rwa [totF_val])
    rw [← totF_val ι e]; apply tprovable_iff_provable.mp
    unfold totF at ia ib ⊢
    refine ?_ ⨀ ia ⨀ ib
    apply exs_imp!
    nrm
    apply exs_imp_ctx!
    nrm
    refine ?_ ⨀ tM_ex hF (e.shift.shift) 1 0
    apply exs_imp!
    nrm
    refine imp_exs_of₃! (&'0) ?_
    nrm
    refine imp_exs₂_of₃! (&'1) (&'2) ?_
    nrm
    cl_prover

end PalomarI3380.Calibration.ArithmeticInterpretation
