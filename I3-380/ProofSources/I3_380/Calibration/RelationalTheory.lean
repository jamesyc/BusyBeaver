module
public import I3_380.Calibration.OperationGraphs
public import I3_380.Calibration.ArithmeticConsequences
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic


def operationAxioms : Theory GraphLanguage :=
  (Set.range fun f : (Σ k, FunctionSymbol k) => operationTotal f.2) ∪
    (Set.range fun f : (Σ k, FunctionSymbol k) => operationUnique f.2)

def markerExists : FFL.FirstOrder.Sentence GraphLanguage :=
  ∃¹ (⊤ : Semisentence GraphLanguage 1)

def graphAxioms : Theory GraphLanguage :=
  {p | p ∈ markerExists :: (filterSentence :: Manifest.preceding.map equationSentence).map graphFormula}

def graphTheory : Theory GraphLanguage :=
  (𝗘𝗤 GraphLanguage ∪ operationAxioms) ∪ graphAxioms

instance : 𝗘𝗤 GraphLanguage ⪯ graphTheory :=
  FFL.Entailment.WeakerThan.ofSubset fun _ mem => Or.inl (Or.inl mem)

theorem graphTheory_finite : Set.Finite graphTheory := by
  letI : Fintype (Σ k, FunctionSymbol k) := Language.Finite.func (L := FilterLanguage)
  have finiteOps : Set.Finite operationAxioms :=
    Set.Finite.union (Set.finite_range _) (Set.finite_range _)
  exact (Theory.EqAxiom.finite.union finiteOps).union (List.finite_toSet _)

noncomputable instance graphTheory_delta : graphTheory.Δ₁ :=
  Theory.Δ₁.ofFinite _ graphTheory_finite


theorem graphTheory_has_operations {A : Type} [Nonempty A] [Tarski.Structure GraphLanguage A]
    [Tarski.Structure.Eq GraphLanguage A] (model : A↓[GraphLanguage] ⊧* graphTheory) :
    HasOperationGraphs (A := A) where
  total symbol := (operationTotal_eval symbol).mp
    ((models_theory_iff.mp model) _ (Or.inl (Or.inr (Or.inl ⟨⟨_,symbol⟩,rfl⟩))))
  unique symbol args a b first second := (operationUnique_eval symbol).mp
    ((models_theory_iff.mp model) _ (Or.inl (Or.inr (Or.inr ⟨⟨_,symbol⟩,rfl⟩))))
      a b args first second

theorem graphTheory_of_filter {A : Type} [Nonempty A] [Tarski.Structure FilterLanguage A]
    [Tarski.Structure.Eq FilterLanguage A] (model : A↓[FilterLanguage] ⊧* filterTheory) :
    letI := graphStructure (A := A)
    A↓[GraphLanguage] ⊧* graphTheory := by
  letI := graphStructure (A := A)
  letI : Tarski.Structure.Eq GraphLanguage A := graphStructure_eq
  apply models_theory_iff.mpr
  rintro p ((equality | (⟨⟨k,symbol⟩,rfl⟩ | ⟨⟨k,symbol⟩,rfl⟩)) | transported)
  · exact models_theory_iff.mp (inferInstance : A↓[GraphLanguage] ⊧* 𝗘𝗤 GraphLanguage) p equality
  · apply (operationTotal_eval symbol).mpr
    intro args
    refine ⟨Tarski.Structure.func (L := FilterLanguage) symbol args,?_⟩
    rfl
  · apply (operationUnique_eval symbol).mpr
    intro a b args ha hb
    exact ha.trans hb.symm
  · rcases List.mem_cons.mp transported with rfl | originalMember
    · simp [markerExists,models_iff]
    · obtain ⟨original,mem,rfl⟩ := List.mem_map.mp originalMember
      have h : original.Evalb (![] : Fin 0 → A) := (models_theory_iff.mp model) _ (Or.inr mem)
      exact (graphFormula_eval original _).mpr h

theorem filterTheory_of_graph {A : Type} [Nonempty A] [structure' : Tarski.Structure GraphLanguage A]
    [Tarski.Structure.Eq GraphLanguage A] (model : A↓[GraphLanguage] ⊧* graphTheory) :
    letI := restoreStructure (graphTheory_has_operations model)
    A↓[FilterLanguage] ⊧* filterTheory := by
  let graphs := graphTheory_has_operations model
  letI := restoreStructure graphs
  letI : Tarski.Structure.Eq FilterLanguage A := restoreStructure_eq graphs
  have restored : @graphStructure A (restoreStructure graphs) = structure' :=
    restoreStructure_relational graphs
  apply models_theory_iff.mpr
  rintro p (equality | member)
  · exact models_theory_iff.mp (inferInstance : A↓[FilterLanguage] ⊧* 𝗘𝗤 FilterLanguage) p equality
  · let φ := graphFormula p
    have member' : φ ∈ graphTheory := Or.inr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,member,rfl⟩))
    have truth : @Semiformula.Evalb GraphLanguage A 0 structure' (![] : Fin 0 → A) φ :=
      (models_theory_iff.mp model) _ member'
    rw [← restored] at truth
    exact (graphFormula_eval p (![] : Fin 0 → A)).mp truth

end PalomarI3380.Calibration
