module
public import I3_380.Calibration.ReadFilterArithmetic
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Logic.Expanded
open ArithmeticInterpretation (Reads InterpFacts)

theorem graphTheory_reads {A : Type} [Nonempty A] [structure' : Tarski.Structure GraphLanguage A]
    [Tarski.Structure.Eq GraphLanguage A] (model : A↓[GraphLanguage] ⊧* graphTheory) :
    ∃ (B : Type) (arithmetic : ORingStructure B) (project : A → B),
      ∀ e, @Reads filterInterpretation A B structure' arithmetic e project := by
  let graphs := graphTheory_has_operations model
  letI : Tarski.Structure FilterLanguage A := restoreStructure graphs
  letI : Tarski.Structure.Eq FilterLanguage A := restoreStructure_eq graphs
  have restored : @graphStructure A (restoreStructure graphs) = structure' :=
    restoreStructure_relational graphs
  obtain ⟨C,inhabited,source⟩ := source_model_of_filterTheory (filterTheory_of_graph model)
  let env := fun _ : Nat => Classical.choice inhabited
  have zfc : Logic.ZFCModel C.mem := fun p h =>
    source p (h.elim Or.inl (fun choice => Or.inr (Or.inl choice)))
  obtain ⟨w,omega⟩ := zfc.omega env
  let domain : OmegaDomain (ClassAxioms.from_ordinary zfc) inhabited := ⟨w,omega⟩
  obtain ⟨default,_⟩ := C.asPoint_onto (env 0)
  refine ⟨domain.Points,inferInstance,readValue C domain,fun e => ?_⟩
  have semantics := reads_filter_arithmetic C domain e default
  change @Reads filterInterpretation A domain.Points (graphStructure (A := A)) inferInstance e (readValue C domain)
    at semantics
  rw [restored] at semantics
  exact semantics

theorem graphTheory_proves_of_reads (p : FFL.FirstOrder.Sentence GraphLanguage)
    (valid : ∀ (A B : Type) [Nonempty A] [Tarski.Structure GraphLanguage A] [ORingStructure B]
      (project : A → B), (∀ e, Reads filterInterpretation e project) → A↓[GraphLanguage] ⊧ p) :
    graphTheory ⊢ p := by
  apply Theory.Proof.complete
  apply consequence_iff_eq.mpr
  intro A _ _ _ model
  obtain ⟨B,arithmetic,project,reads⟩ := graphTheory_reads model
  letI : ORingStructure B := arithmetic
  exact valid A B project reads

theorem interpretation_facts : InterpFacts filterInterpretation graphTheory := by
  constructor <;> (
    apply graphTheory_proves_of_reads
    intro A B _ _ _ project interpretation
    have eq (e a b : A) := (interpretation e).eq a b
    have dom (e a : A) := (interpretation e).dom a
    have zero (e a : A) := (interpretation e).zero a
    have one (e a : A) := (interpretation e).one a
    have addition (e a b c : A) := (interpretation e).add a b c
    have multiplication (e a b c : A) := (interpretation e).mul a b c
    have onto : Function.Surjective project := (interpretation (Classical.arbitrary A)).surj
    simp [models_iff,eq,dom,zero,one,addition,multiplication,Semiformula.eval_substs,
      Semiterm.val,Function.comp_def,Matrix.comp_vecCons',Matrix.constant_eq_singleton] <;>
      first | (intros; apply onto) | (intros; exact (onto _).imp fun _ h => h.symm) | (intros; aesop))

end PalomarI3380.Calibration
