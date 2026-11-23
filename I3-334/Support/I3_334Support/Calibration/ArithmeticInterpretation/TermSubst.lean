module
public import I3_334Support.Calibration.ArithmeticInterpretation.TermFacts
@[expose] public section
/-! # Substituting a term inside a term graph

If `x` is a value of `t`, then the values of `u[t]` are the values of `u[x]`:
`U ⊢ ∀x ∀y (G_t x → (G_{u[t]} y ↔ G_u (y, x)))`. A Σ1 induction on `u`. -/
namespace PalomarI3380.Calibration.ArithmeticInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.FFL.FirstOrder.Entailment

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := GraphLanguage)
local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := GraphLanguage)

variable (ι : Interp)

noncomputable def tsubC (e t u : V) : V :=
  ^∀ ^∀ imp GraphLanguage (subst GraphLanguage (^#1 ∷ 0) (G ι e 0 t))
    (iff GraphLanguage (subst GraphLanguage (^#0 ∷ 0) (G ι e 0 (termSubst ℒₒᵣ (t ∷ 0) u)))
      (subst GraphLanguage (^#0 ∷ ^#1 ∷ 0) (G ι e 1 u)))

instance tsubC_definable : 𝚺ᴬ₁-Function₃ (tsubC ι : V → V → V → V) := by
  unfold tsubC; definability

variable (e : Bootstrapping.Term V GraphLanguage)

noncomputable def tsubF (t : Bootstrapping.Term V ℒₒᵣ) (u : Bootstrapping.Semiterm V ℒₒᵣ 1) :
    Bootstrapping.Formula V GraphLanguage :=
  ∀¹ ∀¹ ((gr ι e t).subst ![#'1] 🡒
    ((gr ι e (u.subst ![t])).subst ![#'0] 🡘 (gr ι e u).subst ![#'0, #'1]))

lemma tsubF_val (t : Bootstrapping.Term V ℒₒᵣ) (u : Bootstrapping.Semiterm V ℒₒᵣ 1) :
    (tsubF ι e t u).val = tsubC ι e.val t.val u.val := by
  simp [tsubF, tsubC]

@[simp] lemma tsubF_shift (t : Bootstrapping.Term V ℒₒᵣ) (u : Bootstrapping.Semiterm V ℒₒᵣ 1) :
    (tsubF ι e t u).shift = tsubF ι e.shift t.shift u.shift := by
  simp [tsubF, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiterm.shift_substs]

/-- The propositional skeleton of the compound case. -/
lemma prop_iff_and {L : Language} [L.Encodable] [L.LORDefinable] {T : InternalTheory V L}
    {c a₁ b₁ a₂ b₂ r : Bootstrapping.Formula V L}
    (h₁ : T ⊢ c 🡒 (a₁ 🡘 b₁)) (h₂ : T ⊢ c 🡒 (a₂ 🡘 b₂)) :
    T ⊢ c 🡒 ((a₁ ⋏ a₂) ⋏ r 🡘 (b₁ ⋏ b₂) ⋏ r) := by
  classical
  cl_prover [h₁, h₂]

variable {ι e} {U : Theory GraphLanguage} [U.Δ₁]

theorem tsub (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage) (t : Bootstrapping.Term V ℒₒᵣ)
    (u : Bootstrapping.Semiterm V ℒₒᵣ 1) : U.internalize V ⊢ tsubF ι e t u := by
  apply tprovable_iff_provable.mpr
  rw [tsubF_val]
  have hC : 𝚺ᴬ₁-Function₁ (fun u : V => tsubC ι e.val t.val u) := by definability
  refine term_ind U (fun u => tsubC ι e.val t.val u) hC ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro z
    rw [Fin.fin_one_eq_zero z, ← tsubF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    have f := all₂_imp! _ (&'0) (&'1) ⨀ (by
      simpa [funF] using TProof.shift! (TProof.shift! (tfun hF e t)))
    have c := all₂_imp! _ (&'0) (&'1) ⨀ (by
      simpa [congF] using TProof.shift! (TProof.shift! (tcong hF e t)))
    have s₁ := tE_symm hF e.shift.shift (&'1) (&'0)
    have s₂ := tE_symm hF e.shift.shift (&'0) (&'1)
    nrm at f c
    simp only [tE] at s₁ s₂
    cl_prover [f, c, s₁, s₂]
  · intro x
    rw [← tsubF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    cl_prover
  · rw [← tsubF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    cl_prover
  · rw [← tsubF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    cl_prover
  · intro a b iha ihb
    have ia : U.internalize V ⊢ tsubF ι e t a := tprovable_iff_provable.mpr (by rwa [tsubF_val])
    have ib : U.internalize V ⊢ tsubF ι e t b := tprovable_iff_provable.mpr (by rwa [tsubF_val])
    rw [← tsubF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    apply exs₂_iff_of!
    nrm
    have ia4 := TProof.shift! (TProof.shift! (TProof.shift! (TProof.shift! ia)))
    have ib4 := TProof.shift! (TProof.shift! (TProof.shift! (TProof.shift! ib)))
    simp only [tsubF_shift] at ia4 ib4
    unfold tsubF at ia4 ib4
    have ia' := all₂_imp! _ (&'1) (&'3) ⨀ ia4
    have ib' := all₂_imp! _ (&'0) (&'3) ⨀ ib4
    nrm at ia' ib'
    exact prop_iff_and ia' ib'
  · intro a b iha ihb
    have ia : U.internalize V ⊢ tsubF ι e t a := tprovable_iff_provable.mpr (by rwa [tsubF_val])
    have ib : U.internalize V ⊢ tsubF ι e t b := tprovable_iff_provable.mpr (by rwa [tsubF_val])
    rw [← tsubF_val ι e]; apply tprovable_iff_provable.mp
    apply TProof.all₂!
    nrm
    apply exs₂_iff_of!
    nrm
    have ia4 := TProof.shift! (TProof.shift! (TProof.shift! (TProof.shift! ia)))
    have ib4 := TProof.shift! (TProof.shift! (TProof.shift! (TProof.shift! ib)))
    simp only [tsubF_shift] at ia4 ib4
    unfold tsubF at ia4 ib4
    have ia' := all₂_imp! _ (&'1) (&'3) ⨀ ia4
    have ib' := all₂_imp! _ (&'0) (&'3) ⨀ ib4
    nrm at ia' ib'
    exact prop_iff_and ia' ib'

end PalomarI3380.Calibration.ArithmeticInterpretation
