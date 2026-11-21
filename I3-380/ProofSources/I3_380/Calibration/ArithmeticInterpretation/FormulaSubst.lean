module
public import I3_380.Calibration.ArithmeticInterpretation.TermSubst
@[expose] public section
/-! # Substituting a term into a translated formula

`U ⊢ J(p[t]) → ∀x (G_t x → J p (x))` for every ℒₒᵣ formula `p` with one bound
variable and every term `t`. Formulas are in negation normal form, so one
direction suffices. The proof is an induction on the complexity of `p` over
all `t` at once (a Π2 induction, in models of PA): the quantifier cases
instantiate the bound variable by a fresh free variable, which shifts `t`. -/
namespace PalomarI3380.Calibration.ArithmeticInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.FFL.FirstOrder.Entailment

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := GraphLanguage)
local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := GraphLanguage)

/-- Propositional skeletons of the connective cases. -/
lemma prop_and {L : Language} [L.Encodable] [L.LORDefinable] {T : InternalTheory V L}
    {a₁ a₂ p₁ p₂ g b₁ b₂ : Bootstrapping.Formula V L}
    (i₁ : T ⊢ a₁ 🡒 p₁) (j₁ : T ⊢ p₁ 🡒 g 🡒 b₁) (i₂ : T ⊢ a₂ 🡒 p₂) (j₂ : T ⊢ p₂ 🡒 g 🡒 b₂) :
    T ⊢ a₁ ⋏ a₂ 🡒 g 🡒 b₁ ⋏ b₂ := by
  classical
  cl_prover [i₁, j₁, i₂, j₂]

lemma prop_or {L : Language} [L.Encodable] [L.LORDefinable] {T : InternalTheory V L}
    {a₁ a₂ p₁ p₂ g b₁ b₂ : Bootstrapping.Formula V L}
    (i₁ : T ⊢ a₁ 🡒 p₁) (j₁ : T ⊢ p₁ 🡒 g 🡒 b₁) (i₂ : T ⊢ a₂ 🡒 p₂) (j₂ : T ⊢ p₂ 🡒 g 🡒 b₂) :
    T ⊢ a₁ ⋎ a₂ 🡒 g 🡒 b₁ ⋎ b₂ := by
  classical
  cl_prover [i₁, j₁, i₂, j₂]

lemma prop_all {L : Language} [L.Encodable] [L.LORDefinable] {T : InternalTheory V L}
    {a d j₀ p g j₁ : Bootstrapping.Formula V L}
    (hA : T ⊢ a 🡒 ∼d ⋎ j₀) (i : T ⊢ j₀ 🡒 p) (hi : T ⊢ p 🡒 g 🡒 j₁) :
    T ⊢ a 🡒 g 🡒 ∼d ⋎ j₁ := by
  classical
  cl_prover [hA, i, hi]

lemma prop_exs {L : Language} [L.Encodable] [L.LORDefinable] {T : InternalTheory V L}
    {d j₀ p g j₁ : Bootstrapping.Formula V L}
    (i : T ⊢ j₀ 🡒 p) (hi : T ⊢ p 🡒 g 🡒 j₁) :
    T ⊢ d ⋏ j₀ 🡒 g 🡒 d ⋏ j₁ := by
  classical
  cl_prover [i, hi]

def IsF₁ (p : V) : Prop := IsSemiformula ℒₒᵣ 1 p
def IsT₀ (t : V) : Prop := IsSemiterm ℒₒᵣ 0 t
def IsE₀ (e : V) : Prop := IsSemiterm GraphLanguage 0 e
def ProvC (U : Theory GraphLanguage) [U.Δ₁] (C : V → V → V → V) (e t p : V) : Prop :=
  Bootstrapping.Provable U (C e t p)

instance isF₁_definable : 𝚫ᴬ₁-Predicate (IsF₁ : V → Prop) := by unfold IsF₁; definability
instance isF₁_definable' (Γ m) : Γᴬ_[m + 1]-Predicate (IsF₁ : V → Prop) :=
  isF₁_definable.of_deltaOne
instance isT₀_definable : 𝚫ᴬ₁-Predicate (IsT₀ : V → Prop) := by unfold IsT₀; definability
instance isT₀_definable' (Γ m) : Γᴬ_[m + 1]-Predicate (IsT₀ : V → Prop) :=
  isT₀_definable.of_deltaOne

instance isE₀_definable : 𝚫ᴬ₁-Predicate (IsE₀ : V → Prop) := by unfold IsE₀; definability
instance isE₀_definable' (Γ m) : Γᴬ_[m + 1]-Predicate (IsE₀ : V → Prop) :=
  isE₀_definable.of_deltaOne

lemma provC_definable (U : Theory GraphLanguage) [U.Δ₁] (C : V → V → V → V) (hC : 𝚺ᴬ₁-Function₃ C) :
    𝚺ᴬ₁-Relation₃ (ProvC U C) := by
  haveI := hC; unfold ProvC; definability

variable (ι : Interp)

noncomputable def subC (e t p : V) : V :=
  imp GraphLanguage (J ι e 0 (subst ℒₒᵣ (t ∷ 0) p)) (^∀ imp GraphLanguage (G ι e 0 t) (J ι e 1 p))

instance subC_definable : 𝚺ᴬ₁-Function₃ (subC ι : V → V → V → V) := by
  unfold subC; definability

noncomputable def subF (e : Bootstrapping.Term V GraphLanguage) (t : Bootstrapping.Term V ℒₒᵣ)
    (p : Bootstrapping.Semiformula V ℒₒᵣ 1) : Bootstrapping.Formula V GraphLanguage :=
  jt ι e (p.subst ![t]) 🡒 ∀¹ (gr ι e t 🡒 jt ι e p)

lemma subF_val (e : Bootstrapping.Term V GraphLanguage) (t : Bootstrapping.Term V ℒₒᵣ)
    (p : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (subF ι e t p).val = subC ι e.val t.val p.val := by
  simp [subF, subC]

lemma imp_of_iff_of {L : Language} [L.Encodable] [L.LORDefinable] {T : InternalTheory V L}
    {c x y : Bootstrapping.Formula V L} (h : T ⊢ c 🡒 (x 🡘 y)) : T ⊢ x 🡒 c 🡒 y := by
  classical
  exact FFL.Entailment.C_swap (FFL.Entailment.C_trans h FFL.Entailment.and₁)

private lemma neg_imp_of_iff_of {L : Language} [L.Encodable] [L.LORDefinable] {T : InternalTheory V L}
    {c x y : Bootstrapping.Formula V L} (h : T ⊢ c 🡒 (x 🡘 y)) : T ⊢ ∼x 🡒 c 🡒 ∼y := by
  classical
  open FFL.Entailment in
  exact C_swap (C_trans (C_trans h and₂) CCCNN)

lemma imp_imp_all! {L : Language} [L.Encodable] [L.LORDefinable] {T : InternalTheory V L}
    {c d : Bootstrapping.Formula V L} {φ : Bootstrapping.Semiformula V L 1}
    (h : T ⊢ c.shift 🡒 d.shift 🡒 φ.free) : T ⊢ c 🡒 d 🡒 ∀¹ φ := by
  classical
  apply FFL.Entailment.CC_of_CK
  apply imp_all!
  rw [Bootstrapping.Semiformula.shift_and]
  exact FFL.Entailment.CK_of_CC h

/-- Normal form for translated formulas. -/
macro "nrmJ" : tactic => `(tactic| simp [Bootstrapping.Semiformula.free, jt_subst, SemitermVec.q,
  Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs,
  Bootstrapping.Semiterm.shift_substs, ← Bootstrapping.Semiterm.bShift_shift_comm,
  one_add_one_eq_two, num3, num4])
macro "nrmJ" " at" h:(ppSpace colGt ident)+ : tactic => `(tactic| simp [Bootstrapping.Semiformula.free,
  jt_subst, SemitermVec.q, Bootstrapping.Semiformula.shift_substs,
  Bootstrapping.Semiformula.substs_substs, Bootstrapping.Semiterm.shift_substs,
  ← Bootstrapping.Semiterm.bShift_shift_comm, one_add_one_eq_two, num3, num4] at $h*)

variable {ι} {U : Theory GraphLanguage} [U.Δ₁]

/-- Atoms: the values of `a[t]`, `b[t]` are those of `a[x]`, `b[x]`. -/
lemma atom_eq (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage) (t : Bootstrapping.Term V ℒₒᵣ)
    (a b : Bootstrapping.Semiterm V ℒₒᵣ 1) :
    U.internalize V ⊢ (gr ι e t).free 🡒
      ((jt ι e (a.subst ![t] ≐ b.subst ![t])).shift 🡘 (jt ι e (a ≐ b)).free) := by
  simp [Bootstrapping.Semiformula.free, jt_subst, jt_equals, SemitermVec.q,
    Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs,
    Bootstrapping.Semiterm.shift_substs]
  apply exs₂_iff_of!
  nrm
  have ia := all₂_imp! _ (&'1) (&'2) ⨀ (by
    simpa [tsubF] using TProof.shift! (TProof.shift! (TProof.shift! (tsub hF e t a))))
  have ib := all₂_imp! _ (&'0) (&'2) ⨀ (by
    simpa [tsubF] using TProof.shift! (TProof.shift! (TProof.shift! (tsub hF e t b))))
  nrm at ia ib
  exact prop_iff_and ia ib

lemma atom_lt (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage) (t : Bootstrapping.Term V ℒₒᵣ)
    (a b : Bootstrapping.Semiterm V ℒₒᵣ 1) :
    U.internalize V ⊢ (gr ι e t).free 🡒
      ((jt ι e (a.subst ![t] <' b.subst ![t])).shift 🡘 (jt ι e (a <' b)).free) := by
  simp [Bootstrapping.Semiformula.free, jt_subst, jt_lessThan, SemitermVec.q,
    Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs,
    Bootstrapping.Semiterm.shift_substs]
  apply exs₂_iff_of!
  nrm
  have ia := all₂_imp! _ (&'1) (&'2) ⨀ (by
    simpa [tsubF] using TProof.shift! (TProof.shift! (TProof.shift! (tsub hF e t a))))
  have ib := all₂_imp! _ (&'0) (&'2) ⨀ (by
    simpa [tsubF] using TProof.shift! (TProof.shift! (TProof.shift! (tsub hF e t b))))
  nrm at ia ib
  exact prop_iff_and ia ib

end

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := GraphLanguage)
local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := GraphLanguage)

/-- Induction on the complexity of formulas with one bound variable, for all markers and
terms at once. -/
theorem complexity_ind (U : Theory GraphLanguage) [U.Δ₁] (C : V → V → V → V) (hC : 𝚺ᴬ₁-Function₃ C)
    (H : ∀ p : Bootstrapping.Semiformula V ℒₒᵣ 1,
      (∀ q : Bootstrapping.Semiformula V ℒₒᵣ 1,
        formulaComplexity ℒₒᵣ q.val < formulaComplexity ℒₒᵣ p.val →
        ∀ (e : Bootstrapping.Term V GraphLanguage) (t : Bootstrapping.Term V ℒₒᵣ),
          Bootstrapping.Provable U (C e.val t.val q.val)) →
      ∀ (e : Bootstrapping.Term V GraphLanguage) (t : Bootstrapping.Term V ℒₒᵣ),
        Bootstrapping.Provable U (C e.val t.val p.val))
    (p : Bootstrapping.Semiformula V ℒₒᵣ 1) (e : Bootstrapping.Term V GraphLanguage)
    (t : Bootstrapping.Term V ℒₒᵣ) :
    Bootstrapping.Provable U (C e.val t.val p.val) := by
  have key : ∀ d : V, ∀ p : V, IsF₁ p → formulaComplexity ℒₒᵣ p ≤ d →
      ∀ e : V, IsE₀ e → ∀ t : V, IsT₀ t → ProvC U C e t p := by
    have : ∀ Γ, Γᴬ_[1 + 1]-Relation₃ (ProvC U C) :=
      fun _ => .of_lt (provC_definable U C hC) (by simp)
    refine InductionOnHierarchy.order_induction_sigma 𝚷 (1 + 1) ?_ ?_
    · definability
    intro d ih p hp hd e he t ht
    have := H ⟨p, by simpa [IsF₁] using hp⟩ (fun q hq e' t' => ih _ (lt_of_lt_of_le hq hd) q.val
      (by simpa [IsF₁] using q.isSemiformula) le_rfl e'.val (by simpa [IsE₀] using e'.isSemiterm)
      t'.val (by simpa [IsT₀] using t'.isSemiterm))
      ⟨e, by simpa [IsE₀] using he⟩ ⟨t, by simpa [IsT₀] using ht⟩
    simpa [ProvC] using this
  exact key _ p.val (by simpa [IsF₁] using p.isSemiformula) le_rfl e.val
    (by simpa [IsE₀] using e.isSemiterm) t.val (by simpa [IsT₀] using t.isSemiterm)

variable {ι : Interp} {U : Theory GraphLanguage} [U.Δ₁]

theorem formula_subst (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage)
    (t : Bootstrapping.Term V ℒₒᵣ) (p : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    U.internalize V ⊢ subF ι e t p := by
  apply tprovable_iff_provable.mpr
  rw [subF_val]
  refine complexity_ind U (subC ι) inferInstance ?_ p e t
  intro p ih e t
  have IH : ∀ q : Bootstrapping.Semiformula V ℒₒᵣ 1,
      formulaComplexity ℒₒᵣ q.val < formulaComplexity ℒₒᵣ p.val →
      ∀ (e : Bootstrapping.Term V GraphLanguage) (t : Bootstrapping.Term V ℒₒᵣ),
        U.internalize V ⊢ subF ι e t q :=
    fun q hq e t => tprovable_iff_provable.mpr (by rw [subF_val]; exact ih q hq e t)
  rw [← subF_val]; apply tprovable_iff_provable.mp
  rcases IsSemiformula.case_iff.mp p.isSemiformula with
    ⟨k, R, v, hR, hv, hpe⟩ | ⟨k, R, v, hR, hv, hpe⟩ | hpe | hpe | ⟨q₁, q₂, h₁, h₂, hpe⟩ |
      ⟨q₁, q₂, h₁, h₂, hpe⟩ | ⟨q, hq, hpe⟩ | ⟨q, hq, hpe⟩
  · rcases isRel_iff_LOR.mp hR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    let a : Bootstrapping.Semiterm V ℒₒᵣ 1 := ⟨v.[0], hv.nth (show (0 : V) < 2 by simp)⟩ <;>
    let b : Bootstrapping.Semiterm V ℒₒᵣ 1 := ⟨v.[1], hv.nth (show (1 : V) < 2 by simp [one_lt_two])⟩
    · have hp : p = (a ≐ b) := by ext; rw [hpe]; simp [a, b, qqEQ, vec2_eq' hv.lh]; rfl
      subst hp
      unfold subF
      simp only [Arithmetic.substs_equals]
      apply imp_all!
      have k := atom_eq hF e t a b
      simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_imp,
        Bootstrapping.Semiformula.substs_imp] at k ⊢
      exact imp_of_iff_of k
    · have hp : p = (a <' b) := by ext; rw [hpe]; simp [a, b, qqLT, vec2_eq' hv.lh]; rfl
      subst hp
      unfold subF
      simp only [Arithmetic.substs_lessThan]
      apply imp_all!
      have k := atom_lt hF e t a b
      simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_imp,
        Bootstrapping.Semiformula.substs_imp] at k ⊢
      exact imp_of_iff_of k
  · rcases isRel_iff_LOR.mp hR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    let a : Bootstrapping.Semiterm V ℒₒᵣ 1 := ⟨v.[0], hv.nth (show (0 : V) < 2 by simp)⟩ <;>
    let b : Bootstrapping.Semiterm V ℒₒᵣ 1 := ⟨v.[1], hv.nth (show (1 : V) < 2 by simp [one_lt_two])⟩
    · have hp : p = Bootstrapping.Semiterm.notEquals a b := by
        ext; rw [hpe]; simp [a, b, qqNEQ, vec2_eq' hv.lh, Bootstrapping.Semiterm.notEquals]; rfl
      subst hp
      unfold subF
      simp only [Arithmetic.substs_notEquals, jt_notEquals]
      apply imp_all!
      have k := atom_eq hF e t a b
      simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_imp,
        Bootstrapping.Semiformula.substs_imp, Bootstrapping.Semiformula.shift_neg,
        Bootstrapping.Semiformula.substs_neg] at k ⊢
      exact neg_imp_of_iff_of k
    · have hp : p = Bootstrapping.Semiterm.notLessThan a b := by
        ext; rw [hpe]; simp [a, b, qqNLT, vec2_eq' hv.lh, Bootstrapping.Semiterm.notLessThan]; rfl
      subst hp
      unfold subF
      simp only [Arithmetic.substs_notLessThan, jt_notLessThan]
      apply imp_all!
      have k := atom_lt hF e t a b
      simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_imp,
        Bootstrapping.Semiformula.substs_imp, Bootstrapping.Semiformula.shift_neg,
        Bootstrapping.Semiformula.substs_neg] at k ⊢
      exact neg_imp_of_iff_of k
  · have hp : p = ⊤ := by ext; simp [hpe]
    subst hp
    have h : U.internalize V ⊢ ∀¹ (gr ι e t 🡒 ⊤) := by
      apply TProof.all!
      simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_imp,
        Bootstrapping.Semiformula.substs_imp, Bootstrapping.Semiformula.shift_verum,
        Bootstrapping.Semiformula.substs_verum]
      cl_prover
    simp only [subF, Bootstrapping.Semiformula.substs_verum, jt_verum]
    cl_prover [h]
  · have hp : p = ⊥ := by ext; simp [hpe]
    subst hp
    simp only [subF, Bootstrapping.Semiformula.substs_falsum, jt_falsum]
    cl_prover
  · let Q₁ : Bootstrapping.Semiformula V ℒₒᵣ 1 := ⟨q₁, h₁⟩
    let Q₂ : Bootstrapping.Semiformula V ℒₒᵣ 1 := ⟨q₂, h₂⟩
    have hp : p = Q₁ ⋏ Q₂ := by ext; simp [hpe, Q₁, Q₂]
    have c₁ : formulaComplexity ℒₒᵣ Q₁.val < formulaComplexity ℒₒᵣ p.val := by
      rw [hp]; simp [Q₁, Q₂, h₁.isUFormula, h₂.isUFormula]
    have c₂ : formulaComplexity ℒₒᵣ Q₂.val < formulaComplexity ℒₒᵣ p.val := by
      rw [hp]; simp [Q₁, Q₂, h₁.isUFormula, h₂.isUFormula]
    have i₁ := TProof.shift! (IH Q₁ c₁ e t)
    have i₂ := TProof.shift! (IH Q₂ c₂ e t)
    rw [hp]
    unfold subF at i₁ i₂ ⊢
    simp only [Bootstrapping.Semiformula.substs_and, jt_and]
    apply imp_all!
    have a₁ := all_imp! (T := U.internalize V) ((gr ι e t).shift 🡒 (jt ι e Q₁).shift) (&'0)
    have a₂ := all_imp! (T := U.internalize V) ((gr ι e t).shift 🡒 (jt ι e Q₂).shift) (&'0)
    simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_imp,
      Bootstrapping.Semiformula.substs_imp, Bootstrapping.Semiformula.shift_all,
      Bootstrapping.Semiformula.shift_and, Bootstrapping.Semiformula.substs_and] at i₁ i₂ a₁ a₂ ⊢
    exact prop_and i₁ a₁ i₂ a₂
  · let Q₁ : Bootstrapping.Semiformula V ℒₒᵣ 1 := ⟨q₁, h₁⟩
    let Q₂ : Bootstrapping.Semiformula V ℒₒᵣ 1 := ⟨q₂, h₂⟩
    have hp : p = Q₁ ⋎ Q₂ := by ext; simp [hpe, Q₁, Q₂]
    have c₁ : formulaComplexity ℒₒᵣ Q₁.val < formulaComplexity ℒₒᵣ p.val := by
      rw [hp]; simp [Q₁, Q₂, h₁.isUFormula, h₂.isUFormula]
    have c₂ : formulaComplexity ℒₒᵣ Q₂.val < formulaComplexity ℒₒᵣ p.val := by
      rw [hp]; simp [Q₁, Q₂, h₁.isUFormula, h₂.isUFormula]
    have i₁ := TProof.shift! (IH Q₁ c₁ e t)
    have i₂ := TProof.shift! (IH Q₂ c₂ e t)
    rw [hp]
    unfold subF at i₁ i₂ ⊢
    simp only [Bootstrapping.Semiformula.substs_or, jt_or]
    apply imp_all!
    have a₁ := all_imp! (T := U.internalize V) ((gr ι e t).shift 🡒 (jt ι e Q₁).shift) (&'0)
    have a₂ := all_imp! (T := U.internalize V) ((gr ι e t).shift 🡒 (jt ι e Q₂).shift) (&'0)
    simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_imp,
      Bootstrapping.Semiformula.substs_imp, Bootstrapping.Semiformula.shift_all,
      Bootstrapping.Semiformula.shift_or, Bootstrapping.Semiformula.substs_or] at i₁ i₂ a₁ a₂ ⊢
    exact prop_or i₁ a₁ i₂ a₂
  · have hq2 : IsSemiformula ℒₒᵣ ((2 : ℕ) : V) q := by simpa [one_add_one_eq_two] using hq
    let Q : Bootstrapping.Semiformula V ℒₒᵣ 2 := ⟨q, hq2⟩
    have hp : p = ∀¹ Q := by ext; simp [hpe, Q]
    let Q' : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
      Q.shift.shift.subst ![Bootstrapping.Semiterm.fvar 0, Bootstrapping.Semiterm.bvar 0]
    have c : formulaComplexity ℒₒᵣ Q'.val < formulaComplexity ℒₒᵣ p.val := by
      rw [hp]
      simp only [Q', Bootstrapping.Semiformula.val_substs, Bootstrapping.Semiformula.val_shift,
        Bootstrapping.Semiformula.val_all]
      rw [fomulaComplexity_substs (by simpa using Q.shift.shift.isSemiformula)
        (SemitermVec.isSemitermVec _), formulaComplexity_shift (by simpa using Q.shift.isUFormula),
        formulaComplexity_shift Q.isUFormula, formulaComplexity_all Q.isUFormula]
      simp
    have i := IH Q' c e.shift.shift t.shift.shift
    rw [hp]
    unfold subF at i ⊢
    apply imp_all!
    nrmJ
    apply imp_imp_all!
    nrmJ
    have hA := all_imp! (T := U.internalize V)
      ((∼tdom ι e ⋎ jt ι e (Q.subst ![Bootstrapping.Semiterm.bvar 0, t.bShift])).shift.shift) (&'0)
    have hi := all_imp! (T := U.internalize V) (gr ι e.shift.shift t.shift.shift 🡒 jt ι e.shift.shift Q') (&'1)
    simp only [Q'] at hi i
    nrmJ at hA hi i
    exact prop_all hA i hi
  · have hq2 : IsSemiformula ℒₒᵣ ((2 : ℕ) : V) q := by simpa [one_add_one_eq_two] using hq
    let Q : Bootstrapping.Semiformula V ℒₒᵣ 2 := ⟨q, hq2⟩
    have hp : p = ∃¹ Q := by ext; simp [hpe, Q]
    let Q' : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
      Q.shift.shift.subst ![Bootstrapping.Semiterm.fvar 1, Bootstrapping.Semiterm.bvar 0]
    have c : formulaComplexity ℒₒᵣ Q'.val < formulaComplexity ℒₒᵣ p.val := by
      rw [hp]
      simp only [Q', Bootstrapping.Semiformula.val_substs, Bootstrapping.Semiformula.val_shift,
        Bootstrapping.Semiformula.val_exs]
      rw [fomulaComplexity_substs (by simpa using Q.shift.shift.isSemiformula)
        (SemitermVec.isSemitermVec _), formulaComplexity_shift (by simpa using Q.shift.isUFormula),
        formulaComplexity_shift Q.isUFormula, formulaComplexity_ex Q.isUFormula]
      simp
    have i := IH Q' c e.shift.shift t.shift.shift
    rw [hp]
    unfold subF at i ⊢
    nrmJ
    apply exs_imp!
    nrmJ
    apply imp_all!
    nrmJ
    refine imp_exs_of₂! (&'1) ?_
    nrmJ
    have hi := all_imp! (T := U.internalize V) (gr ι e.shift.shift t.shift.shift 🡒 jt ι e.shift.shift Q') (&'0)
    simp only [Q'] at hi i
    nrmJ at hi i
    exact prop_exs i hi

end

end PalomarI3380.Calibration.ArithmeticInterpretation
