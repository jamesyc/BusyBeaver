module
public import I3_380.Calibration.TruthLayerFormulas
public import I3_380.Calibration.AtomTables
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic Logic.Expanded SquareRepresentation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
variable (D : OmegaDomain L inhabited)

scoped instance modelPeano (D : OmegaDomain L inhabited) : D.Points↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano

structure Presentation where
  domain : V
  atoms : V
  domain_natural : ∀ x, E x domain → E x D.omega
  fallback : D.Points
  fallback_in : E fallback.val domain

def Presentation.Carrier (P : Presentation D) := {x : D.Points // E x.val P.domain}

instance (P : Presentation D) : Nonempty (P.Carrier D) := ⟨⟨P.fallback,P.fallback_in⟩⟩

def Presentation.data (P : Presentation D) : TruthData V :=
  ⟨D.omega,P.domain,P.atoms,P.fallback.val⟩

@[instance_reducible] noncomputable def Presentation.interpret (P : Presentation D) : Tarski.Structure GraphLanguage (P.Carrier D) where
  func {_} f _ := f.elim
  rel {_} s v := E (TermWords.atomEntry s (matrixToVec fun i => (v i).val)).val P.atoms

theorem Presentation.of_distinction :
    letI : D.Points↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano
    (TermWords.stagedAlgebra (M := D.Points)).constant .D ≠ TermWords.stagedAlgebra.constant .J →
    ∃ P : Presentation D, letI := P.interpret D; (P.Carrier D)↓[GraphLanguage] ⊧* graphTheory := by
  letI : D.Points↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano
  intro distinct
  let alg := TermWords.stagedAlgebra (M := D.Points)
  have preceding : alg.Models Manifest.preceding := TermWords.quotientAlgebra_preceding
  let laws := RelationLaws.of_model alg preceding
  let left := RelationLaws.support alg (alg.inf (alg.constant .D) (alg.neg (alg.constant .J)))
  let right := RelationLaws.support alg (alg.inf (alg.constant .J) (alg.neg (alg.constant .D)))
  obtain ⟨start,which,proper,subunit⟩ :
      ∃ seed, (seed=left ∨ seed=right) ∧ seed≠alg.zero ∧ alg.le seed (alg.constant .I) := by
    rcases laws.separating_support distinct with l | r
    · exact ⟨left,Or.inl rfl,l,RelationLaws.support_subunit laws.bool _⟩
    · exact ⟨right,Or.inr rfl,r,RelationLaws.support_subunit laws.bool _⟩
  let seed := TermWords.nameClass start
  have nozero : TermWords.canonicalClass seed ≠ alg.zero := by simpa [seed] using proper
  have under : alg.le (TermWords.canonicalClass seed) (alg.constant .I) := by simpa [seed] using subunit
  let filter := TermWords.namedUltrafilter laws seed under nozero
  have member : filter.member start := by
    change alg.le start (alg.constant .I) ∧
      ∃ i : D.Points, alg.le (TermWords.canonicalClass (TermWords.descentAt seed i)) start
    refine ⟨subunit,0,?_⟩
    rw [TermWords.descentAt_zero]
    simpa [seed] using laws.bool.le_refl start
  have separates : filter.member left ∨ filter.member right := by rcases which with h | h <;> simp_all
  obtain ⟨dom,names⟩ := TermWords.canonical_domain D
  obtain ⟨atoms,table⟩ := TermWords.atoms_set D seed
  have bounded : ∀ x, E x dom → E x D.omega := by
    intro x h
    obtain ⟨code,rfl,_⟩ := (names x).mp h
    exact code.property
  have named (code : D.Points) : E code.val dom ↔ TermWords.Canonical code := by
    constructor
    · intro h
      obtain ⟨q,same,ok⟩ := (names _).mp h
      exact (Subtype.ext same : q=code) ▸ ok
    · exact fun h => (names _).mpr ⟨code,rfl,h⟩
  let P : Presentation D := ⟨dom,atoms,bounded,seed.val,(named _).mpr seed.property⟩
  let asName (x : P.Carrier D) : TermWords.CanonicalTerm D.Points := ⟨x.val,(named _).mp x.property⟩
  have bij : Function.Bijective (TermWords.canonicalClass ∘ asName) := by
    constructor
    · intro a b eq
      have equiv : asName a = asName b := TermWords.canonicalClass_injective eq
      exact Subtype.ext (congrArg (fun x : TermWords.CanonicalTerm D.Points => x.val) equiv)
    · intro a
      obtain ⟨code,eq⟩ := TermWords.canonicalClass_surjective a
      exact ⟨⟨code.val,(named _).mpr code.property⟩,eq⟩
  let eq := Equiv.ofBijective _ bij
  letI : Nonempty (TermWords.GroundClasses D.Points) := ⟨start⟩
  letI := structureOf alg filter.member
  letI : Tarski.Structure.Eq FilterLanguage (TermWords.GroundClasses D.Points) := ⟨fun _ _ => Iff.rfl⟩
  have original := graphTheory_of_filter (structureOf_model alg preceding filter separates)
  letI := graphStructure (A := TermWords.GroundClasses D.Points)
  have transported : P.interpret D = Tarski.Structure.ofEquiv (L := GraphLanguage) eq.symm := by
    ext k s entries
    · exact s.elim
    · change GraphSymbol k at s
      change E (TermWords.atomEntry s (matrixToVec fun i => (entries i).val)).val atoms ↔
        Tarski.Structure.rel (L := GraphLanguage) s (fun i => TermWords.canonicalClass (asName (entries i)))
      refine (table s _).trans ?_
      cases s with
      | relation sym =>
        cases sym with
        | chosen =>
          simp only [TermWords.atomTest,matrixToVec_succ,Matrix.vecHead,nth_adjoin_zero]
          exact TermWords.chosenCode_meaning laws seed under nozero (asName (entries 0))
        | equal =>
          simp only [TermWords.atomTest,matrixToVec_succ,Matrix.vecHead,Matrix.vecTail,
            nth_adjoin_zero,nth_adjoin_one]
          change (entries 0).val=(entries 1).val ↔
            TermWords.canonicalClass (asName (entries 0))=TermWords.canonicalClass (asName (entries 1))
          constructor
          · intro same
            exact congrArg TermWords.canonicalClass (Subtype.ext same)
          · intro same
            exact congrArg (fun x : TermWords.CanonicalTerm D.Points => x.val)
              (TermWords.canonicalClass_injective same)
      | operation symbol =>
        exact TermWords.canonicalOperation_eval symbol filter.member (asName ∘ entries)
  refine ⟨P,?_⟩
  letI := P.interpret D
  apply models_theory_iff.mpr
  intro p hp
  have model := (models_theory_iff.mp original) p hp
  change p.Evalb _ 
  rw [transported]
  exact (Tarski.Structure.eval_ofEquiv_iff eq.symm).mpr (by simpa [Matrix.empty_eq,Empty.eq_elim] using (models_iff.mp model))

end PalomarI3380.Calibration.CodedGraph
