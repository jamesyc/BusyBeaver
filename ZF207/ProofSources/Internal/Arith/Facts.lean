module
public import Internal.Arith.Transport
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1
public import Foundation.Meta.ClProver
@[expose] public section
/-! # Facts about the templates

`InterpFacts ι U` lists the standard sentences about the templates that the
substitution lemma uses: the domain is everything, equality is an equivalence,
the operations are total and functional up to equality, and every template
respects equality. Inside a model they become internal theorems of `U`. -/
namespace ZF207.Internal.Arith
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.FFL.FirstOrder.Entailment

/-- The template facts, as standard theorems of `U`, for every marker `e`. -/
structure InterpFacts (ι : Interp) (U : Theory ℒₛₑₜ) : Prop where
  dom_all : U ⊢ “∀ e x, !ι.dom e x”
  eq_refl : U ⊢ “∀ e x, !ι.eq e x x”
  eq_symm : U ⊢ “∀ e x y, !ι.eq e x y → !ι.eq e y x”
  eq_trans : U ⊢ “∀ e x y z, !ι.eq e x y → !ι.eq e y z → !ι.eq e x z”
  zero_ex : U ⊢ “∀ e, ∃ y, !ι.zero e y”
  one_ex : U ⊢ “∀ e, ∃ y, !ι.one e y”
  add_ex : U ⊢ “∀ e a b, ∃ y, !ι.add e a b y”
  mul_ex : U ⊢ “∀ e a b, ∃ y, !ι.mul e a b y”
  zero_fun : U ⊢ “∀ e y z, !ι.zero e y → !ι.zero e z → !ι.eq e y z”
  one_fun : U ⊢ “∀ e y z, !ι.one e y → !ι.one e z → !ι.eq e y z”
  add_fun : U ⊢ “∀ e a b y z, !ι.add e a b y → !ι.add e a b z → !ι.eq e y z”
  mul_fun : U ⊢ “∀ e a b y z, !ι.mul e a b y → !ι.mul e a b z → !ι.eq e y z”
  zero_cong : U ⊢ “∀ e y z, !ι.eq e y z → !ι.zero e y → !ι.zero e z”
  one_cong : U ⊢ “∀ e y z, !ι.eq e y z → !ι.one e y → !ι.one e z”
  add_cong₁ : U ⊢ “∀ e a c b y, !ι.eq e a c → !ι.add e a b y → !ι.add e c b y”
  add_cong₂ : U ⊢ “∀ e a b c y, !ι.eq e b c → !ι.add e a b y → !ι.add e a c y”
  add_cong₃ : U ⊢ “∀ e a b y z, !ι.eq e y z → !ι.add e a b y → !ι.add e a b z”
  mul_cong₁ : U ⊢ “∀ e a c b y, !ι.eq e a c → !ι.mul e a b y → !ι.mul e c b y”
  mul_cong₂ : U ⊢ “∀ e a b c y, !ι.eq e b c → !ι.mul e a b y → !ι.mul e a c y”
  mul_cong₃ : U ⊢ “∀ e a b y z, !ι.eq e y z → !ι.mul e a b y → !ι.mul e a b z”

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

/-- Typed template instances at a marker `e`. -/
noncomputable def tE (e a b : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (⌜ι.eq⌝ : Semiformula V ℒₛₑₜ 3).subst ![e, a, b]
noncomputable def tZ (e a : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (⌜ι.zero⌝ : Semiformula V ℒₛₑₜ 2).subst ![e, a]
noncomputable def tO (e a : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (⌜ι.one⌝ : Semiformula V ℒₛₑₜ 2).subst ![e, a]
noncomputable def tA (e a b c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (⌜ι.add⌝ : Semiformula V ℒₛₑₜ 4).subst ![e, a, b, c]
noncomputable def tM (e a b c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (⌜ι.mul⌝ : Semiformula V ℒₛₑₜ 4).subst ![e, a, b, c]

variable {ι} {U : Theory ℒₛₑₜ} [U.Δ₁]

lemma tE_refl (hF : InterpFacts ι U) (e a : Term V ℒₛₑₜ) : U.internalize V ⊢ tE ι e a a := by
  have h := TProof.specialize₂! (by simpa using internal_provable_of_outer_provable (V := V) hF.eq_refl) a e
  simpa [tE, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tE_symm (hF : InterpFacts ι U) (e a b : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tE ι e a b 🡒 tE ι e b a := by
  have h := TProof.specialize₃! (by simpa using internal_provable_of_outer_provable (V := V) hF.eq_symm) b a e
  simpa [tE, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tE_trans (hF : InterpFacts ι U) (e a b c : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tE ι e a b 🡒 tE ι e b c 🡒 tE ι e a c := by
  have h := TProof.specialize₄! (by simpa using internal_provable_of_outer_provable (V := V) hF.eq_trans) c b a e
  simpa [tE, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tZ_fun (hF : InterpFacts ι U) (e a b : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tZ ι e a 🡒 tZ ι e b 🡒 tE ι e a b := by
  have h := TProof.specialize₃! (by simpa using internal_provable_of_outer_provable (V := V) hF.zero_fun) b a e
  simpa [tE, tZ, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tO_fun (hF : InterpFacts ι U) (e a b : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tO ι e a 🡒 tO ι e b 🡒 tE ι e a b := by
  have h := TProof.specialize₃! (by simpa using internal_provable_of_outer_provable (V := V) hF.one_fun) b a e
  simpa [tE, tO, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tZ_cong (hF : InterpFacts ι U) (e a b : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tE ι e a b 🡒 tZ ι e a 🡒 tZ ι e b := by
  have h := TProof.specialize₃! (by simpa using internal_provable_of_outer_provable (V := V) hF.zero_cong) b a e
  simpa [tE, tZ, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tO_cong (hF : InterpFacts ι U) (e a b : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tE ι e a b 🡒 tO ι e a 🡒 tO ι e b := by
  have h := TProof.specialize₃! (by simpa using internal_provable_of_outer_provable (V := V) hF.one_cong) b a e
  simpa [tE, tO, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

/-- Five-fold specialization. -/
lemma specialize₅! {T : InternalTheory V ℒₛₑₜ} {φ : Semiformula V ℒₛₑₜ 5}
    (b : T ⊢ ∀¹ ∀¹ ∀¹ ∀¹ ∀¹ φ) (t₁ t₂ t₃ t₄ t₅ : Term V ℒₛₑₜ) :
    T ⊢ φ.subst ![t₁, t₂, t₃, t₄, t₅] := by
  have h₁ : T ⊢ (∀¹ ∀¹ ∀¹ ∀¹ φ).subst ![t₅] := TProof.specialize! b t₅
  simp only [Bootstrapping.Semiformula.substs_all] at h₁
  have h₂ := TProof.specialize₄! h₁ t₁ t₂ t₃ t₄
  rw [Bootstrapping.Semiformula.substs_substs] at h₂
  convert h₂ using 2
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_
    (fun i => Fin.cases ?_ (fun i => i.elim0) i) i) i) i) i
  · simp [SemitermVec.q]
  · simp [SemitermVec.q]
  · simp [SemitermVec.q]
  · simp [SemitermVec.q]
  · show t₅ = Bootstrapping.Semiterm.subst ![t₁, t₂, t₃, t₄] t₅.bShift.bShift.bShift.bShift
    rw [Bootstrapping.Semiterm.bShift_substs_succ, Bootstrapping.Semiterm.bShift_substs_succ,
      Bootstrapping.Semiterm.bShift_substs_succ, Bootstrapping.Semiterm.bShift_substs_succ]
    simp

lemma tA_fun (hF : InterpFacts ι U) (e : Term V ℒₛₑₜ) (a b y z : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tA ι e a b y 🡒 tA ι e a b z 🡒 tE ι e y z := by
  have h := specialize₅! (by simpa using internal_provable_of_outer_provable (V := V) hF.add_fun) z y b a e
  simpa [tE, tA, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tM_fun (hF : InterpFacts ι U) (e : Term V ℒₛₑₜ) (a b y z : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tM ι e a b y 🡒 tM ι e a b z 🡒 tE ι e y z := by
  have h := specialize₅! (by simpa using internal_provable_of_outer_provable (V := V) hF.mul_fun) z y b a e
  simpa [tE, tM, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tA_cong₁ (hF : InterpFacts ι U) (e : Term V ℒₛₑₜ) (a c b y : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tE ι e a c 🡒 tA ι e a b y 🡒 tA ι e c b y := by
  have h := specialize₅! (by simpa using internal_provable_of_outer_provable (V := V) hF.add_cong₁) y b c a e
  simpa [tE, tA, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tA_cong₂ (hF : InterpFacts ι U) (e : Term V ℒₛₑₜ) (a b c y : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tE ι e b c 🡒 tA ι e a b y 🡒 tA ι e a c y := by
  have h := specialize₅! (by simpa using internal_provable_of_outer_provable (V := V) hF.add_cong₂) y c b a e
  simpa [tE, tA, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tA_cong₃ (hF : InterpFacts ι U) (e : Term V ℒₛₑₜ) (a b y z : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tE ι e y z 🡒 tA ι e a b y 🡒 tA ι e a b z := by
  have h := specialize₅! (by simpa using internal_provable_of_outer_provable (V := V) hF.add_cong₃) z y b a e
  simpa [tE, tA, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tM_cong₁ (hF : InterpFacts ι U) (e : Term V ℒₛₑₜ) (a c b y : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tE ι e a c 🡒 tM ι e a b y 🡒 tM ι e c b y := by
  have h := specialize₅! (by simpa using internal_provable_of_outer_provable (V := V) hF.mul_cong₁) y b c a e
  simpa [tE, tM, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tM_cong₂ (hF : InterpFacts ι U) (e : Term V ℒₛₑₜ) (a b c y : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tE ι e b c 🡒 tM ι e a b y 🡒 tM ι e a c y := by
  have h := specialize₅! (by simpa using internal_provable_of_outer_provable (V := V) hF.mul_cong₂) y c b a e
  simpa [tE, tM, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

lemma tM_cong₃ (hF : InterpFacts ι U) (e : Term V ℒₛₑₜ) (a b y z : Term V ℒₛₑₜ) :
    U.internalize V ⊢ tE ι e y z 🡒 tM ι e a b y 🡒 tM ι e a b z := by
  have h := specialize₅! (by simpa using internal_provable_of_outer_provable (V := V) hF.mul_cong₃) z y b a e
  simpa [tE, tM, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using h

end

end ZF207.Internal.Arith
