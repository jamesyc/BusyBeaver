module
public import I3_334Support.Calibration.ArithmeticInterpretation.Typed
@[expose] public section
/-! # Typed equations for graphs and translations

Closed (bound-variable-free) terms and formulas only: arity-1 objects are
reduced to these by substituting a variable (`gr_subst₂`, `jt_subst`). -/
namespace PalomarI3380.Calibration.ArithmeticInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := GraphLanguage)
local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := GraphLanguage)

lemma bv2_zero : bv2 (0 : V) = 0 :=
  (IsSemitermVec.empty_iff (L := GraphLanguage) (n := 0 + 2)).mp (bv2_semitermVec 0)
lemma bv3_zero : bv3 (0 : V) = 0 :=
  (IsSemitermVec.empty_iff (L := GraphLanguage) (n := 0 + 3)).mp (bv3_semitermVec 0)

@[simp] lemma tmpl_shift {k : ℕ} (σ : Semisentence GraphLanguage k) :
    (⌜σ⌝ : Bootstrapping.Semiformula V GraphLanguage k).shift = ⌜σ⌝ := by
  ext; simp [tmpl_val]

/-- The domain template at the marker, with one bound variable in front. -/
noncomputable def tdom {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) : Bootstrapping.Semiformula V GraphLanguage (n + 1) :=
  (⌜ι.dom⌝ : Bootstrapping.Semiformula V GraphLanguage 2).subst ![cl e, #'0]

@[simp] lemma tdom_val {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) :
    (tdom ι (n := n) e).val = un (tq ι.dom) e.val (^#0 : V) := by
  simp [tdom, tmpl_val, un]

@[simp] lemma tdom_shift {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) :
    (tdom ι (n := n) e).shift = tdom ι e.shift := by
  simp [tdom, Bootstrapping.Semiformula.shift_substs]

@[simp] lemma tdom_subst {n m : ℕ} (e : Bootstrapping.Term V GraphLanguage) (w : SemitermVec V GraphLanguage (n + 1) m) :
    (tdom ι e).subst w = (⌜ι.dom⌝ : Bootstrapping.Semiformula V GraphLanguage 2).subst ![cl e, w 0] := by
  simp [tdom, Bootstrapping.Semiformula.substs_substs]

/-! ## Translations of connectives -/

@[simp] lemma jt_verum {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) :
    jt ι e (⊤ : Bootstrapping.Semiformula V ℒₒᵣ n) = ⊤ := by ext; simp
@[simp] lemma jt_falsum {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) :
    jt ι e (⊥ : Bootstrapping.Semiformula V ℒₒᵣ n) = ⊥ := by ext; simp
@[simp] lemma jt_and {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) (p q : Bootstrapping.Semiformula V ℒₒᵣ n) :
    jt ι e (p ⋏ q) = jt ι e p ⋏ jt ι e q := by ext; simp
@[simp] lemma jt_or {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) (p q : Bootstrapping.Semiformula V ℒₒᵣ n) :
    jt ι e (p ⋎ q) = jt ι e p ⋎ jt ι e q := by ext; simp
@[simp] lemma jt_neg {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) (p : Bootstrapping.Semiformula V ℒₒᵣ n) :
    jt ι e (∼p) = ∼jt ι e p := by
  ext; simp [J_neg ι _ _ p.isSemiformula _ (closed_semiterm e.isSemiterm_zero _)]
@[simp] lemma jt_all {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) (p : Bootstrapping.Semiformula V ℒₒᵣ (n + 1)) :
    jt ι e (∀¹ p) = ∀¹ (∼tdom ι e ⋎ jt ι e p) := by
  ext; simp [bs_closed e.isSemiterm_zero]
@[simp] lemma jt_exs {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) (p : Bootstrapping.Semiformula V ℒₒᵣ (n + 1)) :
    jt ι e (∃¹ p) = ∃¹ (tdom ι e ⋏ jt ι e p) := by
  ext; simp [bs_closed e.isSemiterm_zero]

lemma jt_notEquals {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) (a b : Bootstrapping.Semiterm V ℒₒᵣ n) :
    jt ι e (Bootstrapping.Semiterm.notEquals a b) = ∼jt ι e (a ≐ b) := by
  rw [← jt_neg, Arithmetic.neg_equals]

lemma jt_notLessThan {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) (a b : Bootstrapping.Semiterm V ℒₒᵣ n) :
    jt ι e (Bootstrapping.Semiterm.notLessThan a b) = ∼jt ι e (a <' b) := by
  rw [← jt_neg, Arithmetic.neg_lessThan]

lemma jt_equals (e : Bootstrapping.Term V GraphLanguage) (a b : Bootstrapping.Term V ℒₒᵣ) :
    jt ι e (a ≐ b) = ∃¹ ∃¹ (((gr ι e a).subst ![#'1] ⋏ (gr ι e b).subst ![#'0]) ⋏
      (⌜ι.eq⌝ : Bootstrapping.Semiformula V GraphLanguage 3).subst ![cl e, #'1, #'0]) := by
  ext
  simp [qqEQ, atomJ, relT, bv2_zero, tmpl_val, bs_closed e.isSemiterm_zero]

lemma jt_lessThan (e : Bootstrapping.Term V GraphLanguage) (a b : Bootstrapping.Term V ℒₒᵣ) :
    jt ι e (a <' b) = ∃¹ ∃¹ (((gr ι e a).subst ![#'1] ⋏ (gr ι e b).subst ![#'0]) ⋏
      (⌜ι.lt⌝ : Bootstrapping.Semiformula V GraphLanguage 3).subst ![cl e, #'1, #'0]) := by
  ext
  simp [qqLT, atomJ, relT, bv2_zero, tmpl_val, eqIndex_ne_ltIndex.symm, bs_closed e.isSemiterm_zero]

/-! ## Graphs of closed terms -/

@[simp] lemma gr_fvar {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) (x : V) :
    gr ι e (Bootstrapping.Semiterm.fvar x : Bootstrapping.Semiterm V ℒₒᵣ n) =
      (⌜ι.eq⌝ : Bootstrapping.Semiformula V GraphLanguage 3).subst ![cl e, #'0, &'x] := by
  ext; simp [eqAt, tmpl_val, bs_closed e.isSemiterm_zero]

@[simp] lemma gr_bvar (e : Bootstrapping.Term V GraphLanguage) :
    gr ι e (Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) =
      (⌜ι.eq⌝ : Bootstrapping.Semiformula V GraphLanguage 3).subst ![cl e, #'0, #'1] := by
  ext; simp [eqAt, tmpl_val, bs_closed e.isSemiterm_zero]

@[simp] lemma gr_zero {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) :
    gr ι e (𝕹 0 : Bootstrapping.Semiterm V ℒₒᵣ n) =
      (⌜ι.zero⌝ : Bootstrapping.Semiformula V GraphLanguage 2).subst ![cl e, #'0] := by
  ext; simp [G_zero, tmpl_val, un, bs_closed e.isSemiterm_zero]

@[simp] lemma gr_one {n : ℕ} (e : Bootstrapping.Term V GraphLanguage) :
    gr ι e (𝕹 1 : Bootstrapping.Semiterm V ℒₒᵣ n) =
      (⌜ι.one⌝ : Bootstrapping.Semiformula V GraphLanguage 2).subst ![cl e, #'0] := by
  ext; simp [G_one, tmpl_val, un, bs_closed e.isSemiterm_zero]

lemma gr_add (e : Bootstrapping.Term V GraphLanguage) (a b : Bootstrapping.Term V ℒₒᵣ) :
    gr ι e (a + b) = ∃¹ ∃¹ (((gr ι e a).subst ![#'1] ⋏ (gr ι e b).subst ![#'0]) ⋏
      (⌜ι.add⌝ : Bootstrapping.Semiformula V GraphLanguage 4).subst ![cl e, #'1, #'0, #'2]) := by
  ext
  simp [G_add ι a.isUTerm b.isUTerm, binG, bv3_zero, tmpl_val, bs_closed e.isSemiterm_zero]

lemma gr_mul (e : Bootstrapping.Term V GraphLanguage) (a b : Bootstrapping.Term V ℒₒᵣ) :
    gr ι e (a * b) = ∃¹ ∃¹ (((gr ι e a).subst ![#'1] ⋏ (gr ι e b).subst ![#'0]) ⋏
      (⌜ι.mul⌝ : Bootstrapping.Semiformula V GraphLanguage 4).subst ![cl e, #'1, #'0, #'2]) := by
  ext
  simp [G_mul ι a.isUTerm b.isUTerm, binG, bv3_zero, tmpl_val, bs_closed e.isSemiterm_zero]

/-- A graph with one bound variable, at two variables. -/
lemma gr_subst₂ (e : Bootstrapping.Term V GraphLanguage) (u : Bootstrapping.Semiterm V ℒₒᵣ 1)
    (a b : Bootstrapping.Term V GraphLanguage) :
    (gr ι e u).subst ![a, b] = (gr ι e (u.subst ![lv b])).subst ![a] := by
  have h := gr_subst ι e ![b] u
  rw [show (lv ⨟ ![b]) = ![lv b] by funext i; rw [Fin.fin_one_eq_zero i]; rfl] at h
  rw [← h, Bootstrapping.Semiformula.substs_substs]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [SemitermVec.q]
  · rw [Fin.fin_one_eq_zero j]; simp [SemitermVec.q]

end PalomarI3380.Calibration.ArithmeticInterpretation
