module
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Theory
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Iteration
@[expose] public section

namespace PalomarI3380.Calibration.Craig

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- A decidable certificate predicate for an axiom enumeration. The
soundness and completeness of the certificate format are proved separately. -/
structure CertificateCheck where
  formula : 𝚫ᴬ₁.Semisentence 2
  proper : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], formula.ProperOn V

variable (check : CertificateCheck)

def paddedAxiom {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p : V) : Prop :=
  ∃ s ≤ p, ∃ w ≤ p, p = s ^⋏ qqVerums w ∧ IsFormula ℒₒᵣ s ∧
    shift ℒₒᵣ s = s ∧ shift ℒₒᵣ p = p ∧ check.formula.val.Evalb ![s,w]

noncomputable def paddedDefinition : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “p. ∃ s <⁺ p, ∃ w <⁺ p, ∃ v, !qqVerumsGraph v w ∧ !qqAndDef p s v ∧
    !(isSemiformula ℒₒᵣ).sigma 0 s ∧ !(shiftGraph ℒₒᵣ) s s ∧ !(shiftGraph ℒₒᵣ) p p ∧
    !check.formula.sigma s w”)
  (.mkPi “p. ∃ s <⁺ p, ∃ w <⁺ p, (∀ v, !qqVerumsGraph v w → !qqAndDef p s v) ∧
    !(isSemiformula ℒₒᵣ).pi 0 s ∧ (∀ t, !(shiftGraph ℒₒᵣ) t s → t = s) ∧
    (∀ t, !(shiftGraph ℒₒᵣ) t p → t = p) ∧ !check.formula.pi s w”)

instance padded_defined {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚫ᴬ₁-Predicate (paddedAxiom check (V := V)) via paddedDefinition check := .mk <| by
  have same (s w : V) : check.formula.pi.val.Evalb ![s,w] ↔ check.formula.val.Evalb ![s,w] :=
    (check.proper V).iff' _
  constructor <;> intro v <;>
    simp [paddedDefinition,paddedAxiom,Bounding.HierarchySymbol.Semiformula.val_sigma,same,eq_comm]

/-- Craig padding keeps the unpadded sentence and the certificate below
the code of the new axiom. -/
def paddedTheory : ArithmeticTheory := {φ | paddedAxiom check (⌜φ⌝ : Nat)}

theorem sentence_of_closedCode {L : Language} [L.Encodable] [L.LORDefinable] (p : Proposition L)
    (closed : shift L (⌜p⌝ : Nat) = ⌜p⌝) :
    ∃ σ : FFL.FirstOrder.Sentence L, p = ↑σ := by
  have fixed : Rewriting.shift p = p :=
    (Semiformula.quote_inj_iff (V := Nat)).mp (by rw [Semiformula.quote_shift]; exact closed)
  have empty := Semiformula.freeVariables_eq_empty_of_shift_eq fixed
  exact ⟨p.toEmpty empty,(Semiformula.emb_toEmpty p empty).symm⟩

noncomputable instance paddedTheory_delta1 : (paddedTheory check).Δ₁ where
  ch := paddedDefinition check
  mem_iff φ := by
    have h := padded_defined check (V := Nat)
    refine (h.df ![(⌜φ⌝ : Nat)]).trans ?_
    constructor
    · intro condition
      have ⟨_,_,_,_,_,_,_,closed,_⟩ := condition
      obtain ⟨σ,rfl⟩ := sentence_of_closedCode φ closed
      exact ⟨σ,by simpa [paddedTheory,Sentence.quote_def] using condition,rfl⟩
    · rintro ⟨σ,mem,rfl⟩
      simpa [paddedTheory,Sentence.quote_def] using mem
  isDelta1 := Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _ <|
    fun V _ _ => (padded_defined check (V := V)).proper

theorem paddedAxiom_iff {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p : V) :
    p ∈ Theory.Δ₁Class (V := V) (paddedTheory check) ↔ paddedAxiom check p := by
  exact (padded_defined check (V := V)).df ![p]

def verums : Nat → ArithmeticSentence
  | 0 => ⊤
  | n+1 => ⊤ ⋏ verums n

theorem verums_quote (n : Nat) : (⌜verums n⌝ : Nat) = qqVerums n := by
  induction n with
  | zero => simp [verums,Sentence.quote_verum]
  | succ n ih => simp [verums,qqVerums_succ,ih,Sentence.quote_verum]

theorem padding_mem (φ : ArithmeticSentence) (certificate : Nat)
    (accepted : check.formula.val.Evalb ![(⌜φ⌝ : Nat),certificate]) :
    φ ⋏ verums certificate ∈ paddedTheory check := by
  change paddedAxiom check (⌜φ ⋏ verums certificate⌝ : Nat)
  have code : (⌜φ ⋏ verums certificate⌝ : Nat) = ⌜φ⌝ ^⋏ qqVerums certificate := by
    simp only [Sentence.quote_and,verums_quote]
  refine ⟨_,?_,certificate,?_,code,Sentence.quote_isSemiformula₀ φ,
    Sentence.shift_quote φ,Sentence.shift_quote _,accepted⟩
  · rw [code]
    exact Arithmetic.le_def.mpr (Or.inr (lt_K!_left _ _))
  · rw [code]
    apply Arithmetic.le_def.mpr
    right
    have strict : (qqVerums certificate : Nat) < ⌜φ⌝ ^⋏ qqVerums certificate := lt_K!_right _ _
    rcases Arithmetic.le_def.mp (le_qqVerums certificate) with same | earlier
    · exact Eq.mp (congrArg (fun x : Nat => x < ⌜φ⌝ ^⋏ qqVerums certificate) same.symm) strict
    · exact lt_trans earlier strict

theorem proves_of_certificate (φ : ArithmeticSentence) (certificate : Nat)
    (accepted : check.formula.val.Evalb ![(⌜φ⌝ : Nat),certificate]) :
    (paddedTheory check) ⊢ φ := by
  apply Theory.Proof.small_complete
  apply consequence_iff.mpr
  intro V _ _ model
  have both : V↓[ℒₒᵣ] ⊧ φ ∧ V↓[ℒₒᵣ] ⊧ verums certificate := by
    simpa [models_iff] using models_theory_iff.mp model _ (padding_mem check φ certificate accepted)
  exact both.1

theorem quote_padding_shape (p : ArithmeticSentence) (s witness : Nat)
    (code : (⌜p⌝ : Nat) = s ^⋏ qqVerums witness) :
    ∃ source : ArithmeticSentence,
      p = source ⋏ verums witness ∧ (⌜source⌝ : Nat) = s := by
  have tag := congrArg (fun x : Nat => π₁ (x-1)) code
  cases p with
  | and a b =>
    change (⌜a ⋏ b⌝ : Nat) = s ^⋏ qqVerums witness at code
    have payload : (⌜a⌝ : Nat) = s ∧ (⌜b⌝ : Nat) = qqVerums witness :=
      (qqAnd_inj _ _ _ _).mp (by simpa only [Sentence.quote_and] using code)
    have padding : b = verums witness :=
      Sentence.quote_inj_iff.mp (payload.2.trans (verums_quote witness).symm)
    exact ⟨a,by rw [padding]; rfl,payload.1⟩
  | falsum =>
    change π₁ ((⌜(⊥ : ArithmeticSentence)⌝ : Nat)-1) = _ at tag
    simp [Sentence.quote_falsum,qqFalsum,qqAnd] at tag
  | verum =>
    change π₁ ((⌜(⊤ : ArithmeticSentence)⌝ : Nat)-1) = _ at tag
    simp [Sentence.quote_verum,qqVerum,qqAnd] at tag
  | or a b =>
    change π₁ ((⌜a ⋎ b⌝ : Nat)-1) = _ at tag
    simp [Sentence.quote_or,qqOr,qqAnd] at tag
  | all a =>
    change π₁ ((⌜∀¹ a⌝ : Nat)-1) = _ at tag
    simp [Sentence.quote_all,qqAll,qqAnd] at tag
  | exs a =>
    change π₁ ((⌜∃¹ a⌝ : Nat)-1) = _ at tag
    simp [Sentence.quote_ex,qqExs,qqAnd] at tag
  | rel | nrel =>
    simp [Sentence.quote_def,qqRel,qqNRel,qqAnd] at tag

theorem unpad {p : ArithmeticSentence} (h : p ∈ paddedTheory check) :
    ∃ source : ArithmeticSentence, ∃ witness : Nat,
      p = source ⋏ verums witness ∧ check.formula.val.Evalb ![(⌜source⌝ : Nat),witness] := by
  obtain ⟨code,_,witness,_,shape,_,_,_,admitted⟩ := h
  obtain ⟨source,padded,eq⟩ := quote_padding_shape p code witness shape
  exact ⟨source,witness,padded,eq.symm ▸ admitted⟩

end PalomarI3380.Calibration.Craig
