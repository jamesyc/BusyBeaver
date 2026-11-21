module
public import I3_380.TruthRecursion
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic

variable {A V : Type} {M : Algebra A} (N : SetContext M V)

/-- A row of a set-valued recursion is formed by separation from an
assignment space. The key supplies that space and the layer's parameters. -/
def LayerUpdate (layer : V → V → V → V → Prop) (key i prior result : V) : Prop :=
  ∃ space data, Internal.OrderedPair N.mem space data key ∧
    ∀ x, N.mem x result ↔ N.mem x space ∧ layer data i prior x

theorem layerUpdate_definable {layer : V → V → V → V → Prop}
    (definable : Definable.Relation4 N layer) :
    Definable.Relation4 N (N.LayerUpdate layer) := by
  intro n k i f r hk hi hf hr
  have unpack := Definable.orderedPair (N := N) (n := n+2) (i := 1) (j := 0) (k := k+2)
    (by omega) (by omega) (by omega)
  have result := Definable.mem (N := N) (n := n+3) (i := 0) (j := r+3) (by omega) (by omega)
  have space := Definable.mem (N := N) (n := n+3) (i := 0) (j := 2) (by omega) (by omega)
  have row := definable (n := n+3) (i := 1) (j := i+3) (k := f+3) (l := 0)
    (by omega) (by omega) (by omega) (by omega)
  exact Definable.ex (Definable.ex (unpack.and (Definable.all (result.iff (space.and row)))))

theorem layerUpdate_exists {layer : V → V → V → V → Prop} (definable : Definable.Relation4 N layer)
    (space data i prior : V) :
    ∃ result, N.LayerUpdate layer (N.orderedPair space data) i prior result := by
  have description := definable (n := 5) (i := 2) (j := 3) (k := 4) (l := 0)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨result,meaning⟩ := N.separate [data,i,prior] description space space
  exact ⟨result,space,data,N.orderedPair_intro _ _,meaning⟩

theorem layerUpdate_unique {layer : V → V → V → V → Prop} {key i prior a b : V}
    (first : N.LayerUpdate layer key i prior a) (second : N.LayerUpdate layer key i prior b) :
    a=b := by
  obtain ⟨s,d,spec,first⟩ := first
  obtain ⟨t,e,read,second⟩ := second
  obtain ⟨eqS,eqD⟩ := Internal.orderedPair_injective spec read
  subst t
  subst e
  exact N.ext _ _ (fun x => (first x).trans (second x).symm)

/-- Recursion along an internal ordinal, with each row a subset of a
fixed set. The step receives precisely the graph of the earlier rows. -/
theorem setValuedRecursion {domain : V} (ordinal : N.Ordinal domain)
    {layer : V → V → V → V → Prop} (definable : Definable.Relation4 N layer) (space data : V) :
    ∃ family, ∀ i, N.mem i domain →
      ∃ past, N.Restricts family i past ∧
        ∀ x, N.FamilyTruth family i x ↔ N.mem x space ∧ layer data i past x := by
  let R : SetRecursion N :=
    ⟨domain,domain,N.orderedPair space data,fun _ => N.mem,Definable.membership_relation,
      ordinal.ordered,N.LayerUpdate layer,N.layerUpdate_definable definable,
      N.layerUpdate_exists definable space data,fun _ _ _ _ => N.layerUpdate_unique⟩
  obtain ⟨family,computed⟩ := R.solution_exists
  refine ⟨family,fun i valid => ?_⟩
  obtain ⟨cut,past,value,cutSpec,uses,atValue,step⟩ := computed.agrees i valid
  have cutEq : cut=i := N.ext cut i fun z =>
    (cutSpec z).trans ⟨And.right,fun hz => ⟨ordinal.transitive i valid z hz,hz⟩⟩
  subst cut
  obtain ⟨s,d,key,membership⟩ := step
  obtain ⟨eqS,eqD⟩ := Internal.orderedPair_injective key (N.orderedPair_intro space data)
  subst s
  subst d
  obtain ⟨_,_,unique⟩ := computed.functionOn.1 i valid
  refine ⟨past,uses,fun x => Iff.trans ?_ (membership x)⟩
  exact ⟨fun ⟨row,read,yes⟩ => ((unique row read).trans (unique value atValue).symm) ▸ yes,
    fun yes => ⟨value,atValue,yes⟩⟩

end PalomarI3380.SquareRepresentation.SetContext
