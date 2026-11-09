module

public import PA215PA.Theory
public import PA213PA.InternalCodedSourceCandidate

@[expose] public section
namespace PA213.PA.InternalTrace.CodedSource
open PA215 PA215.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open SourceCommandEncodingInternal

noncomputable def sourceEnumerationFormula : ArithmeticSemisentence 1 :=
  “i. ∀ c initial, !commandRelationGraph c 0 0 initial →
    ∃ k cs d result, !enumerationGraph result i initial ∧ !traceGraph k cs c d ∧ !commandRelationGraph d i 0 result”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
theorem sourceEnumeration_correct (i : V) :
    (V ⊧/![i] sourceEnumerationFormula) ↔
      ∀c initial : V, CommandRelation c 0 0 initial →
        ∃k cs d,Trace k cs c d ∧ CommandRelation d i 0 (enumerationValue i initial) := by
  simp [sourceEnumerationFormula,commandRelation_correct,enumeration_graph,trace_correct]

/-- Every model-valued number of fresh candidates is realized by an actual
literal source trace. The invariant carries both candidate N and residual L. -/
theorem source_enumeration (i c initial : V) (h : CommandRelation c 0 0 initial) :
    ∃k cs d,Trace k cs c d ∧ CommandRelation d i 0 (enumerationValue i initial) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀i : V,∀c initial : V, CommandRelation c 0 0 initial →
      ∃k cs d,Trace k cs c d ∧ CommandRelation d i 0 (enumerationValue i initial) := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun i : V=>∀c initial : V, CommandRelation c 0 0 initial →
        ∃k cs d,Trace k cs c d ∧ CommandRelation d i 0 (enumerationValue i initial)) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb sourceEnumerationFormula,by trivial,?_⟩
      intro i; simpa using (sourceEnumeration_correct i).symm
    · intro c initial h
      exact ⟨0,?[c],c,trace_zero c,by simpa only [enumeration_zero] using h⟩
    · intro i ih c initial h
      obtain ⟨k,cs,d,ht,hd⟩ := ih c initial h
      obtain ⟨m,ds,e,hu,he⟩ := source_candidate d i (enumerationValue i initial) hd
      obtain ⟨es,hv⟩ := trace_compose ht hu
      exact ⟨k+m,es,e,hv,by simpa only [enumeration_succ] using he⟩
  exact all i c initial h

/-- The exact V1 accepted refutation forces literal source halting from any
clean root store with candidate and residual zero. No source-simulation premise remains. -/
theorem refutation_root_halts (code xs : V) (hv : ValidStore xs) (hc : CommandClean xs)
    (hn : registers xs 0=0) (hl : registers xs 8=0)
    (hcode : ActualCheckerBlueprint.verifyValue code=2) :
    ∃k cs d,Trace k cs (stateCode 1 xs) d ∧ control d=0 := by
  have hr := commandRelation_root xs hv hc
  rw [hn,hl] at hr
  obtain ⟨k,cs,d,ht,hd⟩ := source_enumeration (ActualCandidateBlueprint.candidateValue code+1)
    (stateCode 1 xs) (commandState xs) hr
  rw [refutation_enumeration_halts code _ hcode] at hd
  exact ⟨k,cs,d,ht,commandRelation_zero _ _ _ hd⟩
#print axioms sourceEnumeration_correct
#print axioms source_enumeration
#print axioms refutation_root_halts
end PA213.PA.InternalTrace.CodedSource

