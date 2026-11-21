module
public import I0451.Logic.SetLanguageCodes
public import I0451.Logic.Tait.Codes
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
@[expose] public section
/-! # Translation of internal set-theoretic formulas into native codes

`tr ⟪env, d, m, f⟫ p` translates an internal `ℒₛₑₜ` formula `p` into the pair
`⟪χ p, χ (∼p)⟫` of native codes. Computing both components at once makes `χ (∼p)`
literally the negation of `χ p` (or conversely).

Labels: free variable `&i` is the label `Y (m + i)`; bound variable `#j` is entry
`j` of the label vector `env`; a quantifier at depth `d` binds the label
`X f d` and pushes it onto `env`. The family `f ∈ {0, 1}` keeps the bound labels
of two translations of the same formula apart. Bound labels along a branch are
distinct, and never equal to a free label, so each binder's label is foreign to
everything outside its scope. Label `0` is never used: it occurs in the falsity
code `1`. -/
namespace I0451.Logic.Tait
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The label of free variable `i`. -/
noncomputable def ylab (i : V) : V := ⟪0, i⟫ + 1
/-- Labels reserved by the translation's binder-renaming lemmas. -/
noncomputable def rlab (k : V) : V := ⟪1, k⟫ + 1
/-- The label bound at depth `d` in family `f`. -/
noncomputable def xlab (f d : V) : V := ⟪f + 2, d⟫ + 1

theorem lt_xlab (family depth : V) : depth < xlab family depth := by
  unfold xlab
  exact lt_of_le_of_lt (le_pair_right _ _) (lt_add_one _)

noncomputable abbrev ceqv (a b : V) : V := eqc a b

/-- Relation code 0 is equality. Relation code 1 is membership. -/
noncomputable def atomL (R a b : V) : V :=
  if R = 0 then ceqv a b else mem a b

/-- Components of the parameter `⟪env, d, m, f⟫`. -/
noncomputable def penv (x : V) : V := π₁ x
noncomputable def pdep (x : V) : V := π₁ (π₂ x)
noncomputable def poff (x : V) : V := π₁ (π₂ (π₂ x))
noncomputable def pfam (x : V) : V := π₂ (π₂ (π₂ x))

@[simp] lemma penv_mk (e d m f : V) : penv ⟪e, d, m, f⟫ = e := by simp [penv]
@[simp] lemma pdep_mk (e d m f : V) : pdep ⟪e, d, m, f⟫ = d := by simp [pdep]
@[simp] lemma poff_mk (e d m f : V) : poff ⟪e, d, m, f⟫ = m := by simp [poff]
@[simp] lemma pfam_mk (e d m f : V) : pfam ⟪e, d, m, f⟫ = f := by simp [pfam]

/-- The label of a variable term. -/
noncomputable def vlab (env m t : V) : V :=
  if π₁ (t - 1) = 0 then env.[π₂ (t - 1)] else ylab (m + π₂ (t - 1))

@[simp] lemma vlab_bvar (env m i : V) : vlab env m ^#i = env.[i] := by
  simp [vlab, qqBvar]

@[simp] lemma vlab_fvar (env m i : V) : vlab env m ^&i = ylab (m + i) := by
  simp [vlab, qqFvar]

/-- The atom for relation `R` (`0` is equality, `1` membership). -/
noncomputable def atom (env m R t₀ t₁ : V) : V := atomL R (vlab env m t₀) (vlab env m t₁)

/-- Pairs for the positive and negative constructors. -/
noncomputable def posPair (A : V) : V := ⟪A, cneg A⟫
noncomputable def negPair (A : V) : V := ⟪cneg A, A⟫

/-- The parameter under one more binder. -/
noncomputable def step (x : V) : V :=
  ⟪xlab (pfam x) (pdep x) ∷ penv x, pdep x + 1, poff x, pfam x⟫

end

/-! ## Σ1 definitions -/

def ylabDef : 𝚺ᴬ₀.Semisentence 2 := .mkSigma “y i. ∃ p <⁺ y, !pairDef p 0 i ∧ y = p + 1”
def xlabDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma “y f d. ∃ p <⁺ y, !pairDef p (f + 2) d ∧ y = p + 1”
def rlabDef : 𝚺ᴬ₀.Semisentence 2 := .mkSigma “y k. ∃ p <⁺ y, !pairDef p 1 k ∧ y = p + 1”
def penvDef : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “y x. !pi₁Def y x”
def pdepDef : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “y x. ∃ u, !pi₂Def u x ∧ !pi₁Def y u”
def poffDef : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “y x. ∃ u, !pi₂Def u x ∧ ∃ w, !pi₂Def w u ∧ !pi₁Def y w”
def pfamDef : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “y x. ∃ u, !pi₂Def u x ∧ ∃ w, !pi₂Def w u ∧ !pi₂Def y w”

def vlabDef : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y env m t. ∃ u <⁺ t, (t = u + 1 ∨ (t = 0 ∧ u = 0)) ∧ ∃ a, !pi₁Def a u ∧ ∃ i, !pi₂Def i u ∧
    ((a = 0 ∧ !nthDef y env i) ∨ (a ≠ 0 ∧ !ylabDef y (m + i)))”

def atomLDef : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y R a b. (R = 0 ∧ !eqcDef y a b) ∨ (R ≠ 0 ∧ !memDef y a b)”

def atomDef : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “y env m R t₀ t₁. ∃ a, !vlabDef a env m t₀ ∧ ∃ b, !vlabDef b env m t₁ ∧ !atomLDef y R a b”

def posPairDef : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “y A. ∃ n, !negDef n A ∧ !pairDef y A n”
def negPairDef : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “y A. ∃ n, !negDef n A ∧ !pairDef y n A”

def stepDef : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y x. ∃ e, !penvDef e x ∧ ∃ d, !pdepDef d x ∧ ∃ m, !poffDef m x ∧ ∃ f, !pfamDef f x ∧
    ∃ l, !xlabDef l f d ∧ ∃ e', !adjoinDef e' l e ∧ !pair₄Def y e' (d + 1) m f”

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance ylab_defined : 𝚺ᴬ₀-Function₁ (ylab : V → V) via ylabDef := .mk fun v => by
  simp only [ylabDef, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  simp [ylab]
  intro h; rw [h]; simp
instance xlab_defined : 𝚺ᴬ₀-Function₂ (xlab : V → V → V) via xlabDef := .mk fun v => by
  simp only [xlabDef, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  simp [xlab]
  intro h; rw [h]; simp
instance rlab_defined : 𝚺ᴬ₀-Function₁ (rlab : V → V) via rlabDef := .mk fun v => by
  simp only [rlabDef, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  simp [rlab]
  intro h; rw [h]; simp
instance penv_defined : 𝚺ᴬ₁-Function₁ (penv : V → V) via penvDef := .mk fun v => by
  simp [penvDef, penv]
instance pdep_defined : 𝚺ᴬ₁-Function₁ (pdep : V → V) via pdepDef := .mk fun v => by
  simp [pdepDef, pdep]
instance poff_defined : 𝚺ᴬ₁-Function₁ (poff : V → V) via poffDef := .mk fun v => by
  simp [poffDef, poff]
instance pfam_defined : 𝚺ᴬ₁-Function₁ (pfam : V → V) via pfamDef := .mk fun v => by
  simp [pfamDef, pfam]

instance vlab_defined : 𝚺ᴬ₁-Function₃ (vlab : V → V → V → V) via vlabDef := .mk fun v => by
  simp only [vlabDef, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  rcases zero_or_succ (v 3) with h | ⟨u, h⟩
  · by_cases ha : π₁ (0 : V) = 0 <;> simp [h, vlab, ha, ylab_defined.iff]
  · have e : ∀ u' : V, (u + 1 = u' + 1 ∨ (u + 1 = 0 ∧ u' = 0)) ↔ u' = u := fun u' => by
      constructor
      · rintro (h' | ⟨h', _⟩)
        · exact (add_right_cancel h').symm
        · simp at h'
      · rintro rfl; exact Or.inl rfl
    by_cases ha : π₁ u = 0 <;> simp [h, vlab, ha, e, ylab_defined.iff]

instance atomL_defined : 𝚺ᴬ₁-Function₃ (atomL : V → V → V → V) via atomLDef := .mk fun v => by
  by_cases h : v 1 = 0 <;> simp [atomLDef, atomL, h, eqc_defined.iff, mem_defined.iff]

instance atom_defined : 𝚺ᴬ₁-Function₅ (atom : V → V → V → V → V → V) via atomDef :=
  .mk fun v => by simp [atomDef, atom, vlab_defined.iff, atomL_defined.iff]

instance posPair_defined : 𝚺ᴬ₁-Function₁ (posPair : V → V) via posPairDef := .mk fun v => by
  simp [posPairDef, posPair]

instance negPair_defined : 𝚺ᴬ₁-Function₁ (negPair : V → V) via negPairDef := .mk fun v => by
  simp [negPairDef, negPair]

instance step_defined : 𝚺ᴬ₁-Function₁ (step : V → V) via stepDef := .mk fun v => by
  simp [stepDef, step, penv_defined.iff, pdep_defined.iff, poff_defined.iff, pfam_defined.iff]

end

/-! ## The construction -/

namespace Tr

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ e, !penvDef e param ∧ ∃ m, !poffDef m param ∧
    ∃ t₀, !nthDef t₀ v 0 ∧ ∃ t₁, !nthDef t₁ v 1 ∧ ∃ A, !atomDef A e m R t₀ t₁ ∧
    !posPairDef y A”
  nrel := .mkSigma “y param k R v. ∃ e, !penvDef e param ∧ ∃ m, !poffDef m param ∧
    ∃ t₀, !nthDef t₀ v 0 ∧ ∃ t₁, !nthDef t₁ v 1 ∧ ∃ A, !atomDef A e m R t₀ t₁ ∧
    !negPairDef y A”
  verum := .mkSigma “y param. ∃ t, !negDef t 1 ∧ !posPairDef y t”
  falsum := .mkSigma “y param. ∃ t, !negDef t 1 ∧ !negPairDef y t”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. ∃ a, !pi₁Def a y₁ ∧ ∃ b, !pi₁Def b y₂ ∧
    ∃ c, !andDef c a b ∧ !posPairDef y c”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. ∃ a, !pi₂Def a y₁ ∧ ∃ b, !pi₂Def b y₂ ∧
    ∃ c, !andDef c a b ∧ !negPairDef y c”
  all := .mkSigma “y param p₁ ys. ∃ r, !nthDef r ys 0 ∧ ∃ P, !pi₁Def P r ∧
    ∃ d, !pdepDef d param ∧ ∃ f, !pfamDef f param ∧ ∃ l, !xlabDef l f d ∧
    ∃ Q, !allDef Q l P ∧ !posPairDef y Q”
  exs := .mkSigma “y param p₁ ys. ∃ r, !nthDef r ys 0 ∧ ∃ N, !pi₂Def N r ∧
    ∃ d, !pdepDef d param ∧ ∃ f, !pfamDef f param ∧ ∃ l, !xlabDef l f d ∧
    ∃ Q, !allDef Q l N ∧ !negPairDef y Q”
  allChanges := .mkSigma “param' param i. !stepDef param' param”
  exsChanges := .mkSigma “param' param i. !stepDef param' param”

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel param _ R v := posPair (atom (penv param) (poff param) R v.[0] v.[1])
  nrel param _ R v := negPair (atom (penv param) (poff param) R v.[0] v.[1])
  verum _ := posPair (cneg (1 : V))
  falsum _ := negPair (cneg (1 : V))
  and _ _ _ y₁ y₂ := posPair (cand (π₁ y₁) (π₁ y₂))
  or _ _ _ y₁ y₂ := negPair (cand (π₂ y₁) (π₂ y₂))
  all param _ ys := posPair (all (xlab (pfam param) (pdep param)) (π₁ ys.[0]))
  exs param _ ys := negPair (all (xlab (pfam param) (pdep param)) (π₂ ys.[0]))
  allChanges param _ := step param
  exsChanges param _ := step param
  rel_defined := .mk fun v => by
    simp [blueprint, atom_defined.iff, posPair_defined.iff, penv_defined.iff, poff_defined.iff]
  nrel_defined := .mk fun v => by
    simp [blueprint, atom_defined.iff, negPair_defined.iff, penv_defined.iff, poff_defined.iff]
  verum_defined := .mk fun v => by simp [blueprint, posPair_defined.iff]
  falsum_defined := .mk fun v => by simp [blueprint, negPair_defined.iff]
  and_defined := .mk fun v => by simp [blueprint, posPair_defined.iff]
  or_defined := .mk fun v => by simp [blueprint, negPair_defined.iff]
  all_defined := .mk fun v => by
    simp [blueprint, posPair_defined.iff, pdep_defined.iff, pfam_defined.iff]
  exs_defined := .mk fun v => by
    simp [blueprint, negPair_defined.iff, pdep_defined.iff, pfam_defined.iff]
  allChanges_defined := .mk fun v => by simp [blueprint, step_defined.iff]
  exChanges_defined := .mk fun v => by simp [blueprint, step_defined.iff]

end Tr

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The translation pair `⟪χ p, χ (∼p)⟫`. -/
noncomputable def tr (param p : V) : V := Tr.construction.result ℒₛₑₜ param p

/-- The translation of `p` with bound-label vector `env`, depth `d`, free-label
offset `m` and family `f`. -/
noncomputable def chi (env d m f p : V) : V := π₁ (tr ⟪env, d, m, f⟫ p)

end

end I0451.Logic.Tait
