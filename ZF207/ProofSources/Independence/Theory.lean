module
public import Independence.Interpretation
public import FoundationGateSemantics
public import ConcreteArithmeticProofTransport
@[expose] public section
/-! # The gate theory `S` and the arithmetic theory `T₀`

`S` consists of Foundation's equality axioms, an axiom asserting an object with
no members, and the machine's gate for every equality-free formula code. `T₀`
collects the arithmetic sentences σ such that `S` proves `J` of σ read in ω.

This file proves three calibration premises for `T₀`, all semantically:
* every arithmetic sentence that ZF proves in ω is a theorem of `T₀`;
* `𝗜𝚺₁ ⪯ T₀`;
* `T₀` is consistent if ZF is.

`T₀` itself is not Δ₁; the Craig-coded theory used for Foundation's theorem has
the same theorems. -/
namespace ZF207.Independence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory FFL.Entailment
open ZF207.GateModel ZF207.OmegaInterpretation ZFR.FoundationBridge

/-- The gate axiom for a formula code `A` and labels `d`, `h`. -/
noncomputable def gateSentence (A : CF) (d h : ℕ) : Sentence ℒₛₑₜ :=
  (ofSource 0 (ZFR.positivePointedSource A.code d h)).univCl

/-- Some object has no members. -/
def emptySentence : Sentence ℒₛₑₜ := “∃ e, ∀ y, y ∉ e”

/-- The axioms of `S`. -/
inductive SAxiom : Sentence ℒₛₑₜ → Prop
  | eq {σ : Sentence ℒₛₑₜ} : σ ∈ (𝗘𝗤 _ : SetTheory) → SAxiom σ
  | empty : SAxiom emptySentence
  | gate (A : CF) (d h : ℕ) : A.EqFree → A.code ≠ d → A.code ≠ h → d ≠ h →
      SAxiom (gateSentence A d h)

/-- The gate theory. -/
def S : SetTheory := Set.ofPred SAxiom

instance : (𝗘𝗤 _ : SetTheory) ⪯ S := Entailment.WeakerThan.ofSubset fun _ h => SAxiom.eq h

lemma mixed_zero {V : Type*} (b : Fin 0 → V) (s : ℕ → V) : mixedAssignment 0 b s = s := by
  funext i; simp [mixedAssignment]

lemma eval_gateSentence {V : Type*} [SetStructure V] [Nonempty V] (A : CF) (d h : ℕ) :
    V↓[ℒₛₑₜ] ⊧ gateSentence A d h ↔
      ∀ s : ℕ → V, ZFR.eval (fun x y : V => x ∈ y) (ZFR.positivePointedSource A.code d h) s := by
  simp only [models_iff, gateSentence, Semiformula.eval_univCl]
  refine forall_congr' fun s => ?_
  rw [ofSource_eval, mixed_zero]

section Models
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* S]

/-- Models of `S` satisfy the machine's gate. -/
lemma codeGate_of_models : CodeGate (fun x y : W => x ∈ y) := by
  intro A hA d h had hah hdh s
  have hm := Theory.models W S (SAxiom.gate A d h hA had hah hdh)
  exact (eval_positivePointed_distinct _ _ d h had hah hdh s).mp ((eval_gateSentence A d h).mp hm s)

/-- Models of `S` have an object with no members. -/
lemma empty_of_models : ∃ e : W, ∀ y, y ∉ e := by
  simpa [models_iff, emptySentence] using Theory.models W S SAxiom.empty

end Models

/-- The arithmetic sentences whose `J`-reading in ω is provable in `S`. -/
def T₀ : ArithmeticTheory := {σ | S ⊢ J (arithmeticTranslation.translate σ)}

/-- ZF-theorems read in ω are `T₀`-theorems. -/
theorem absorb {ψ : ArithmeticSentence}
    (h : (𝗭𝗙 : SetTheory) ⊢ arithmeticTranslation.translate ψ) : T₀ ⊢ ψ := by
  have hS : S ⊢ J (arithmeticTranslation.translate ψ) := by
    apply SetTheory.complete.{0}
    intro W _ _ _
    have hg := codeGate_of_models (W := W)
    obtain ⟨e₀, he₀⟩ := empty_of_models (W := W)
    haveI := gateHull_of_codeGate he₀ hg
    rw [eval_J]
    intro e he
    exact models_of_provable (gate_interprets_zf (nq_isEmpty he)) h
  exact Entailment.by_axm hS

/-- `T₀` extends Peano arithmetic, hence `𝗜𝚺₁`. -/
theorem pa_weaker : 𝗣𝗔 ⪯ T₀ :=
  weakerThan_iff.mpr fun hp => absorb (pa_proof_to_zf hp)

theorem base : 𝗜𝚺₁ ⪯ T₀ := Entailment.WeakerThan.trans inferInstance pa_weaker

/-- A consistent ZF has a model. -/
lemma exists_zf_model [hZF : Consistent (𝗭𝗙 : SetTheory)] :
    ∃ (V : Type) (_ : SetStructure V) (_ : Nonempty V), V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  by_contra hne
  push Not at hne
  have hbot : (𝗭𝗙 : SetTheory) ⊢ ⊥ :=
    SetTheory.complete.{0} _ ⊥ fun V _ _ hV => (hne V _ _ hV).elim
  exact (consistent_iff_unprovable_bot.mp hZF) hbot

/-- ZF models are models of `S`. -/
instance models_S_of_zf {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    V↓[ℒₛₑₜ] ⊧* S := ⟨fun σ hσ => by
  cases hσ with
  | eq h => exact (inferInstance : V↓[ℒₛₑₜ] ⊧* (𝗘𝗤 _ : SetTheory)).models_set h
  | empty =>
    obtain ⟨e, he⟩ := SetTheory.empty_exists (V := V)
    simpa [models_iff, emptySentence] using ⟨e, he⟩
  | gate A d h _ had hah hdh =>
    exact (eval_gateSentence A d h).mpr fun s => source_positive_valid _ d h had hah hdh s⟩

/-- `T₀` is consistent if ZF is. -/
theorem consistent [Consistent (𝗭𝗙 : SetTheory)] : Consistent T₀ := by
  obtain ⟨V, _, _, _⟩ := exists_zf_model
  have hg := codeGate_of_models (W := V)
  obtain ⟨e, he⟩ := empty_of_models (W := V)
  haveI := gateHull_of_codeGate he hg
  have he' := nq_isEmpty (mem := fun x y : V => x ∈ y) he
  haveI : (WFPart (Q he'))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := gate_interprets_zf he'
  have hA : (arithmeticTranslation.Model (WFPart (Q he')))↓[ℒₒᵣ] ⊧* T₀ := ⟨fun σ hσ => by
    have hJ := models_of_provable (inferInstance : V↓[ℒₛₑₜ] ⊧* S) hσ
    have hN := (eval_J _).mp hJ e he
    have ht := DirectTranslation.Model.translate_iff (π := arithmeticTranslation)
      (M := WFPart (Q he')) (σ := σ)
    rw [interpreted_structure_eq_standard (V := WFPart (Q he'))] at ht
    exact ht.mp hN⟩
  exact consistent_of_model T₀ (arithmeticTranslation.Model (WFPart (Q he')))

end ZF207.Independence
