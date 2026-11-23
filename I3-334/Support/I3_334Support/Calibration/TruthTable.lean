module
public import I3_334Support.Calibration.TruthData
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic Logic.Expanded SquareRepresentation

variable {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
variable (D : OmegaDomain L inhabited)

noncomputable abbrev context (_ : OmegaDomain L inhabited) := L.context inhabited

noncomputable def TruthData.toKey (N : SetContext (ClassRelation.algebra E G) V) (d : TruthData V) : V :=
  N.orderedPair d.omega (N.orderedPair d.domain (N.orderedPair d.atoms d.fallback))

def TruthData.Reads (N : SetContext (ClassRelation.algebra E G) V) (key : V) (d : TruthData V) : Prop :=
  ∃ rest last, Internal.OrderedPair N.mem d.omega rest key ∧
    Internal.OrderedPair N.mem d.domain last rest ∧ Internal.OrderedPair N.mem d.atoms d.fallback last

theorem TruthData.reads_key (N : SetContext (ClassRelation.algebra E G) V) (d : TruthData V) :
    d.Reads N (d.toKey N) :=
  ⟨_,_,N.orderedPair_intro ..,N.orderedPair_intro ..,N.orderedPair_intro ..⟩

theorem TruthData.reads_unique {N : SetContext (ClassRelation.algebra E G) V}
    {key : V} {d e : TruthData V} (first : d.Reads N key) (second : e.Reads N key) : d=e := by
  obtain ⟨r,l,p,q,s⟩ := first
  obtain ⟨r',l',p',q',s'⟩ := second
  obtain ⟨omega,rfl⟩ := Internal.orderedPair_injective p p'
  obtain ⟨domain,rfl⟩ := Internal.orderedPair_injective q q'
  obtain ⟨atoms,fallback⟩ := Internal.orderedPair_injective s s'
  cases d
  cases e
  simp_all

def FormulaUpdate (N : SetContext (ClassRelation.algebra E G) V) (key p prior env : V) : Prop :=
  ∃ d : TruthData V, d.Reads N key ∧ FormulaLayer N d p prior env

theorem formulaUpdate_definable (laws : ClassAxioms E G) (inhabited : Nonempty V) :
    Definable.Relation4 (laws.context inhabited) (FormulaUpdate (laws.context inhabited)) := by
  let N := laws.context inhabited
  intro n key i f e hk hi hf he
  have first := Definable.orderedPair (N := N) (n := n+6) (i := 5) (j := 1) (k := key+6)
    (by omega) (by omega) (by omega)
  have second := Definable.orderedPair (N := N) (n := n+6) (i := 4) (j := 0) (k := 1)
    (by omega) (by omega) (by omega)
  have third := Definable.orderedPair (N := N) (n := n+6) (i := 3) (j := 2) (k := 0)
    (by omega) (by omega) (by omega)
  have settings := Definable.ex (Definable.ex (first.and (second.and third)))
  have meaning := formulaLayer_formula laws inhabited (n := n+4) (w := 3) (d := 2) (t := 1) (u := 0)
    (i := i+4) (f := f+4) (e := e+4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  apply (Definable.ex (Definable.ex (Definable.ex (Definable.ex (settings.and meaning))))).congr
  intro v
  exact ⟨fun ⟨w,d,t,u,key,value⟩ => ⟨⟨w,d,t,u⟩,key,value⟩,
    fun ⟨⟨w,d,t,u⟩,key,value⟩ => ⟨w,d,t,u,key,value⟩⟩

structure TruthTable (P : Presentation D) where
  family : V
  row : ∀ p : D.Points, ∃ prior,
    (context D).Restricts family p.val prior ∧
    ∀ env : D.Points, (context D).FamilyTruth family p.val env.val ↔
      FormulaLayer (context D) (P.data D) p.val prior env.val

theorem TruthTable.exists_table (P : Presentation D) : Nonempty (TruthTable D P) := by
  let N := context D
  let data := P.data D
  obtain ⟨family,rows⟩ := N.setValuedRecursion (N.omega_ordinal D.specification)
    (formulaUpdate_definable L inhabited) D.omega (data.toKey N)
  refine ⟨⟨family,fun p => ?_⟩⟩
  obtain ⟨prior,restrict,values⟩ := rows p.val p.property
  refine ⟨prior,restrict,fun env => (values env.val).trans ?_⟩
  constructor
  · rintro ⟨_,other,read,truth⟩
    have eq := TruthData.reads_unique read (data.reads_key N)
    rw [eq] at truth
    exact truth
  · exact fun h => ⟨env.property,data,data.reads_key N,h⟩

def TruthTable.holds {P : Presentation D} (T : TruthTable D P) (p env : D.Points) : Prop :=
  (context D).FamilyTruth T.family p.val env.val

theorem TruthTable.prior_holds {P : Presentation D} (T : TruthTable D P)
    {p : D.Points} {prior : V} (restricted : (context D).Restricts T.family p.val prior)
    {q env : D.Points} (earlier : q < p) :
    (context D).FamilyTruth prior q.val env.val ↔ T.holds D q env :=
  (context D).familyTruth_restrict restricted earlier

end PalomarI3380.Calibration.CodedGraph
