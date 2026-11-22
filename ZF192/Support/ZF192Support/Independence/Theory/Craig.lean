module
public import ZF192Support.Calculus.Internal.DeltaOne
public import ZF192Support.Calculus.Internal.Tait.Instance
@[expose] public section
/-! # Craig-padded theories over C-traces

For a code function `g` with a uniform Σ1 graph, the theory `craigTheory L G` has the axioms
`s ⋏ ⊤ⁿ` where `s` is a sentence and `n` is a `cRule`-trace containing `chiS 0 (g s)`. The
witnesses `s` and `n` are below the axiom, so with the Δ1 trace check the axiom predicate is
Δ1 in every model of `𝗜𝚺₁` (Craig's trick). In a model `V`, the axioms of the theory are
exactly the codes satisfying the same predicate read in `V`. -/
namespace ZF192Support.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZFR.ArithmeticRepresentation
open ZF192Support.Internal.Tait (chiS chiSDef)

/-- A code function on every model of `𝗜𝚺₁` with a uniform Σ1 graph. -/
structure CodeFn where
  graph : 𝚺ᴬ₁.Semisentence 2
  f : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V → V
  defined : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], 𝚺ᴬ₁-Function₁ (f V) via graph

variable (L : Language) [L.Encodable] [L.LORDefinable] (G : CodeFn)

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `p = s ⋏ ⊤ⁿ` with `s` a sentence and `n` a trace containing `chiS 0 (g s)`. -/
def CraigR (p : V) : Prop :=
  ∃ s ≤ p, ∃ n ≤ p, p = s ^⋏ qqVerums n ∧ IsFormula L s ∧ shift L s = s ∧ shift L p = p ∧
    modelTrace cRule n ∧ modelMember (chiS 0 (G.f V s)) n

end

noncomputable def craigΔ : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “p. ∃ s <⁺ p, ∃ n <⁺ p, ∃ v, !qqVerumsGraph v n ∧ !qqAndDef p s v ∧
    !(isSemiformula L).sigma 0 s ∧ !(shiftGraph L) s s ∧ !(shiftGraph L) p p ∧
    !cTraceΔ.sigma n ∧ ∃ k, !G.graph k s ∧ ∃ c, !chiSDef c 0 k ∧ !memberΔ.sigma c n”)
  (.mkPi “p. ∃ s <⁺ p, ∃ n <⁺ p, (∀ v, !qqVerumsGraph v n → !qqAndDef p s v) ∧
    !(isSemiformula L).pi 0 s ∧ (∀ t, !(shiftGraph L) t s → t = s) ∧
    (∀ t, !(shiftGraph L) t p → t = p) ∧
    !cTraceΔ.pi n ∧ ∀ k, !G.graph k s → ∀ c, !chiSDef c 0 k → !memberΔ.pi c n”)

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance craigΔ_defined : 𝚫ᴬ₁-Predicate (CraigR L G (V := V)) via craigΔ L G := by
  have := G.defined V
  exact .mk <| by
    constructor
    · intro v
      simp [craigΔ, Bounding.HierarchySymbol.Semiformula.val_sigma,
        ZF192Support.Internal.Tait.Disj.chiS_defined.iff, eq_comm]
    · intro v
      simp [craigΔ, CraigR, Bounding.HierarchySymbol.Semiformula.val_sigma,
        ZF192Support.Internal.Tait.Disj.chiS_defined.iff, eq_comm]

end

/-- The Craig-padded theory: the sentences whose codes satisfy `CraigR` in `ℕ`. -/
def craigTheory : Theory L := {σ | CraigR L G (⌜σ⌝ : ℕ)}

lemma exists_sentence_of_shift {φ : Proposition L} (h : shift L (⌜φ⌝ : ℕ) = ⌜φ⌝) :
    ∃ σ : Sentence L, φ = ↑σ := by
  have hs : Rewriting.shift φ = φ :=
    (Semiformula.quote_inj_iff (V := ℕ)).mp (by rw [Semiformula.quote_shift]; exact h)
  have hfree := Semiformula.freeVariables_eq_empty_of_shift_eq hs
  exact ⟨φ.toEmpty hfree, (Semiformula.emb_toEmpty φ hfree).symm⟩

noncomputable instance craigTheory_delta1 : Theory.Δ₁ (craigTheory L G) where
  ch := craigΔ L G
  mem_iff φ := by
    have hd := craigΔ_defined L G (V := ℕ)
    change (craigΔ L G).val.Evalb ![(⌜φ⌝ : ℕ)] ↔ _
    refine (hd.df ![(⌜φ⌝ : ℕ)]).trans ?_
    show CraigR L G (⌜φ⌝ : ℕ) ↔ _
    constructor
    · intro h
      obtain ⟨s, -, n, -, -, -, -, hp, -⟩ := id h
      obtain ⟨σ, rfl⟩ := exists_sentence_of_shift L hp
      exact ⟨σ, by simpa [craigTheory, Sentence.quote_def] using h, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      simpa [craigTheory, Sentence.quote_def] using hσ
  isDelta1 := Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
    fun V _ _ => (craigΔ_defined L G (V := V)).proper

/-- In a model, the axioms of the Craig theory are the codes satisfying `CraigR` there. -/
lemma mem_craig_iff {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p : V) :
    p ∈ Theory.Δ₁Class (V := V) (craigTheory L G) ↔ CraigR L G p := by
  change V ⊧/![p] (craigΔ L G).val ↔ _
  exact (craigΔ_defined L G (V := V)).df ![p]

end ZF192Support.Halting
