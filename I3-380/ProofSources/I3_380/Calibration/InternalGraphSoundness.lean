module
public import I3_380.Calibration.ProofValidity
public import I3_380.Calibration.TruthNegation
public import I3_380.Calibration.TruthSubstitution
public import I3_380.Calibration.TruthQuotes
public import I3_380.Calibration.QuotedAxioms
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic.Expanded
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
variable (D : OmegaDomain L inhabited) {P : Presentation D} (T : TruthTable D P)

theorem AssignmentIn.empty : AssignmentIn D (P := P) 0 := by
  intro i h
  exact (not_lt_of_ge (Arithmetic.zero_le i) (by simpa using h)).elim

theorem AssignmentIn.adjoin {f : D.Points} (ready : AssignmentIn D (P := P) f) (x : P.Carrier D) :
    AssignmentIn D (P := P) (x.val ∷ f) := by
  intro i h
  rcases zero_or_succ i with rfl | ⟨i,rfl⟩
  · simpa only [nth_adjoin_zero] using x.property
  · rw [nth_adjoin_succ]
    exact ready i (by simpa [len_adjoin] using h)

theorem AssignmentIn.drop {x f : D.Points} (ready : AssignmentIn D (P := P) (x ∷ f)) :
    AssignmentIn D (P := P) f := by
  intro i h
  have next := ready (i+1) (by simpa only [len_adjoin,add_lt_add_iff_right] using h)
  simpa only [nth_adjoin_succ] using next

theorem AssignmentIn.term_value {term f : D.Points} (ready : AssignmentIn D (P := P) f)
    (wellFormed : IsTerm GraphLanguage term) :
    E (variableValue term ⟪0,f⟫ P.fallback).val P.domain := by
  rcases graph_term_cases.mp wellFormed with ⟨i,h,_⟩ | ⟨i,rfl⟩
  · exact (not_lt_of_ge (Arithmetic.zero_le i) h).elim
  · rw [variableValue_free,lookup]
    split
    · exact ready _ ‹i < len f›
    · exact P.fallback_in

theorem derivationTyped {d s : D.Points} (proof : DerivationOf graphTheory d s) :
    IsFormulaSet GraphLanguage s := by
  rw [← proof.1]
  exact (Derivation.case proof.2).1

open Derivation in
set_option maxHeartbeats 1000000 in
/-- Soundness applies to model-coded proofs of any internal length.
Induction uses Separation in the ambient set model because the truth
table is a set parameter. -/
theorem TruthTable.derivation_sound
    (model : letI := P.interpret D; (P.Carrier D)↓[GraphLanguage] ⊧* graphTheory) :
    ∀ d : D.Points, T.DerivationTrue D d := by
  classical
  obtain ⟨_,formula,meaning⟩ := derivationTrue_definable D T
  apply D.setOrderInduction [D.omega,P.domain,T.family] D.omega _ formula meaning
  intro d ih s proof f ready
  have earlier (b : D.Points) (below : b<d) : T.DerivationTrue D b := ih b below
  have typed := derivationTyped D proof
  have steps := (Derivation.case proof.2).2
  have goal : s=fstIdx d := proof.1.symm
  subst s
  rcases steps with ⟨s,p,rfl,hp,hn⟩ | ⟨s,rfl,h⟩ |
    ⟨s,p,q,dp,dq,rfl,major,first,second⟩ | ⟨s,p,q,d',rfl,major,premise⟩ |
    ⟨s,p,d',rfl,major,premise⟩ | ⟨s,p,t,d',rfl,major,tTerm,premise⟩ |
    ⟨s,d',rfl,subset,premise⟩ | ⟨s,d',rfl,eq,premise⟩ |
    ⟨s,p,dp,dq,rfl,first,second⟩ | ⟨s,p,rfl,member,axiomMember⟩
  · by_cases h : T.holds D p ⟪0,f⟫
    · exact ⟨p,by simpa using hp,h⟩
    · have valid := (typed p (by simpa using hp)).isUFormula
      exact ⟨Bootstrapping.neg GraphLanguage p,by simpa using hn,(T.holds_negation D p valid _).mpr h⟩
  · exact ⟨^⊤,by simpa using h,T.holds_true D _⟩
  · obtain ⟨a,ha,truthA⟩ := earlier dp (by simp) _ first f ready
    obtain ⟨b,hb,truthB⟩ := earlier dq (by simp) _ second f ready
    rcases mem_bitInsert_iff.mp ha with equalA | inSeq
    · rcases mem_bitInsert_iff.mp hb with equalB | inSeq
      · exact ⟨p ^⋏ q,by simpa using major,(T.holds_and D p q _).mpr ⟨equalA ▸ truthA,equalB ▸ truthB⟩⟩
      · exact ⟨b,by simpa using inSeq,truthB⟩
    · exact ⟨a,by simpa using inSeq,truthA⟩
  · obtain ⟨a,belongs,truth⟩ := earlier d' (by simp) _ premise f ready
    rcases mem_bitInsert_iff.mp belongs with equalA | other
    · exact ⟨p ^⋎ q,by simpa using major,(T.holds_or D p q _).mpr (Or.inl (equalA ▸ truth))⟩
    · rcases mem_bitInsert_iff.mp other with equalB | inSeq
      · exact ⟨p ^⋎ q,by simpa using major,(T.holds_or D p q _).mpr (Or.inr (equalB ▸ truth))⟩
      · exact ⟨a,by simpa using inSeq,truth⟩
  · have body : IsSemiformula GraphLanguage 1 p := by
      have h := typed (^∀ p) (by simpa using major)
      simpa using h
    by_contra no
    have all : ∀ x : P.Carrier D, T.holds D p (pushBound x.val ⟪0,f⟫) := by
      intro x
      obtain ⟨q,belongs,truth⟩ := earlier d' (by simp) _ premise (x.val ∷ f) (ready.adjoin D x)
      rcases mem_bitInsert_iff.mp belongs with rfl | other
      · simpa only [pushBound,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair] using
          (T.holds_free D body f x.val).mp truth
      · obtain ⟨original,inside,rfl⟩ := mem_setShift_iff.mp other
        have checked := (typed original (by simpa using inside)).isUFormula
        exact (no ⟨original,by simpa using inside,(T.holds_shift D original checked 0 f x.val).mp truth⟩).elim
    exact no ⟨^∀ p,by simpa using major,(T.holds_all D p _).mpr all⟩
  · have body : IsSemiformula GraphLanguage 1 p := by
      have h := typed (^∃ p) (by simpa using major)
      simpa using h
    obtain ⟨q,belongs,truth⟩ := earlier d' (by simp) _ premise f ready
    rcases mem_bitInsert_iff.mp belongs with rfl | other
    · let value := variableValue t ⟪0,f⟫ P.fallback
      let x : P.Carrier D := ⟨value,ready.term_value D tTerm⟩
      have meaning := (T.holds_substs1 D body tTerm f).mp truth
      refine ⟨^∃ p,by simpa using major,(T.holds_exs D p _).mpr ⟨x,?_⟩⟩
      simpa only [pushBound,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair] using meaning
    · exact ⟨q,by simpa using other,truth⟩
  · obtain ⟨p,belongs,truth⟩ := earlier d' (by simp) _ ⟨rfl,premise⟩ f ready
    exact ⟨p,by simpa using subset belongs,truth⟩
  · have valid := (Derivation.case premise).1
    rcases nil_or_adjoin f with rfl | ⟨x,rest,rfl⟩
    · obtain ⟨p,belongs,truth⟩ := earlier d' (by simp) _ ⟨rfl,premise⟩ 0 (AssignmentIn.empty D)
      have lifted := shift_mem_setShift (L := GraphLanguage) belongs
      refine ⟨shift GraphLanguage p,by simpa [eq] using lifted,?_⟩
      exact (T.holds_shift_of_advance D p (valid _ belongs).isUFormula 0 0 0 (Or.inr ⟨rfl,rfl⟩)).mpr truth
    · obtain ⟨p,belongs,truth⟩ := earlier d' (by simp) _ ⟨rfl,premise⟩ rest (ready.drop D)
      have lifted := shift_mem_setShift (L := GraphLanguage) belongs
      exact ⟨shift GraphLanguage p,by simpa [eq] using lifted,
        (T.holds_shift D p (valid _ belongs).isUFormula 0 rest x).mpr truth⟩
  · obtain ⟨a,belongs,truthA⟩ := earlier dp (by simp) _ first f ready
    obtain ⟨b,other,truthB⟩ := earlier dq (by simp) _ second f ready
    rcases mem_bitInsert_iff.mp belongs with rfl | h
    · rcases mem_bitInsert_iff.mp other with rfl | h
      · have valid := (derivationTyped D first a belongs).isUFormula
        exact ((T.holds_negation D a valid _).mp truthB truthA).elim
      · exact ⟨b,by simpa using h,truthB⟩
    · exact ⟨a,by simpa using h,truthA⟩
  · obtain ⟨φ,axiomOf,rfl⟩ := (graphTheory_quoted p).mp axiomMember
    letI := P.interpret D
    have truthOf := (models_theory_iff.mp model) φ axiomOf
    refine ⟨_,by simpa using member,?_⟩
    have known := (T.holds_quote D φ (![] : Fin 0 → P.Carrier D) f).mpr truthOf
    simpa only [boundVector,matrixToVec_nil] using known

include T in
theorem TruthTable.no_refutation
    (model : letI := P.interpret D; (P.Carrier D)↓[GraphLanguage] ⊧* graphTheory) :
    ¬Provable graphTheory (^⊥ : D.Points) := by
  rintro ⟨d,proof⟩
  obtain ⟨p,member,truth⟩ := T.derivation_sound D model d _ proof 0 (AssignmentIn.empty D)
  have eq : p=(^⊥ : D.Points) := mem_singleton_iff.mp member
  exact T.holds_false D _ (eq ▸ truth)

end PalomarI3380.Calibration.CodedGraph
