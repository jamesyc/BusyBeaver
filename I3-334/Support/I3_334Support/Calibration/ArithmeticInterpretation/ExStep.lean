module
public import I3_334Support.Calibration.ArithmeticInterpretation.FormulaSubst
@[expose] public section
/-! # The existential step

With the template facts, `U` proves `J (p[t]) → J (∃p)` for every formula `p`
with one bound variable and every term `t`: take a value `x` of `t` (totality),
transport `J (p[t])` to `J p (x)` (`formula_subst`), and use that `x` is in the
domain. This discharges `ExStep`, so internal `T`-refutations become internal
`U`-refutations (`provable_falsum`). -/
namespace PalomarI3380.Calibration.ArithmeticInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.FFL.FirstOrder.Entailment

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := GraphLanguage)

variable {ι : Interp} {U : Theory GraphLanguage} [U.Δ₁]

lemma tdom_all (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage) :
    U.internalize V ⊢ ∀¹ (tdom ι (n := 0) e) := by
  have h := TProof.specialize! (by simpa using internal_provable_of_outer_provable (V := V) hF.dom_all) e
  simpa [tdom, Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb, SemitermVec.q,
    Semiformula.substs_substs, Bootstrapping.Semiformula.substs_substs, Matrix.vecHead,
    Matrix.vecTail] using h

lemma prop_final {L : Language} [L.Encodable] [L.LORDefinable] {T : InternalTheory V L}
    {g a p b d x : Bootstrapping.Formula V L}
    (s : T ⊢ a 🡒 p) (i : T ⊢ p 🡒 g 🡒 b) (hd : T ⊢ d) (e : T ⊢ d ⋏ b 🡒 x) :
    T ⊢ g 🡒 a 🡒 x := by
  classical
  cl_prover [s, i, hd, e]

theorem ex_step_typed (hF : InterpFacts ι U) (e : Bootstrapping.Term V GraphLanguage)
    (t : Bootstrapping.Term V ℒₒᵣ) (p : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    U.internalize V ⊢ jt ι e (p.subst ![t]) 🡒 jt ι e (∃¹ p) := by
  have key : U.internalize V ⊢ ∃¹ gr ι e t 🡒 jt ι e (p.subst ![t]) 🡒 jt ι e (∃¹ p) := by
    apply exs_imp!
    have s := TProof.shift! (formula_subst hF e t p)
    have i := all_imp! (T := U.internalize V) (gr ι e.shift t.shift 🡒 jt ι e.shift p.shift) (&'0)
    have hd := TProof.specialize! (tdom_all hF (V := V) e.shift) (&'0)
    have ee := imp_exs! (T := U.internalize V) (tdom ι e.shift ⋏ jt ι e.shift p.shift) (&'0)
    unfold subF at s
    simp only [jt_exs, Bootstrapping.Semiformula.shift_imp, Bootstrapping.Semiformula.shift_exs,
      Bootstrapping.Semiformula.shift_all, Bootstrapping.Semiformula.shift_and,
      Bootstrapping.Semiformula.substs_imp, Bootstrapping.Semiformula.substs_and,
      Bootstrapping.Semiformula.free, gr_shift, jt_shift, tdom_shift, tdom_subst] at s i hd ee ⊢
    exact prop_final s i hd ee
  exact key ⨀ (by simpa [totF] using ttot hF e t)

theorem ex_step (hF : InterpFacts ι U) : ExStep ι U V := by
  intro ε p t he hp ht
  let E : Bootstrapping.Term V GraphLanguage := ⟨ε, by simpa using he⟩
  let P : Bootstrapping.Semiformula V ℒₒᵣ 1 := ⟨p, by simpa using hp⟩
  let T : Bootstrapping.Term V ℒₒᵣ := ⟨t, by simpa using ht⟩
  obtain ⟨d⟩ := ex_step_typed hF E T P
  have d₁ : U.internalize V ⊢!ᵈᵉʳ
      insert (∼jt ι E (P.subst ![T]) ⋎ jt ι E (∃¹ P)) ∅ := by
    rw [← Bootstrapping.Semiformula.imp_def]; exact d
  have := TDerivation.toDerivable (TDerivation.orInv d₁)
  simp [E, P, T, substs1, emptyset_def, J_exs hp.isUFormula, bs_closed he] at this ⊢
  exact this

/-- Stage one: an internal refutation of `T` gives a `U`-derivation of `¬ Mark &x`, when `U`
derives the translated axioms of `T` from the marker and proves the template facts. -/
theorem stage_one (T : ArithmeticTheory) [T.Δ₁] (hF : InterpFacts ι U) (hT : AxStep ι T U V)
    (h : Bootstrapping.Provable T (^⊥ : V)) :
    ∃ x : V, Derivable U (insert (neg GraphLanguage (markAt ι (^&x))) (0 : V)) :=
  refutation_jset ι T U hT (ex_step hF) h

end PalomarI3380.Calibration.ArithmeticInterpretation
