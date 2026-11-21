module
public import I3_380.BoundedChoice
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext.ClassUpdate

open Logic
variable {A V : Type} {M : Algebra A} {N : SetContext M V} (U : ClassUpdate N)

private theorem cut_value {R : SetRecursion N} {i cut : V}
    (spec : R.domain = U.domain) (relation : R.before = N.mem)
    (hi : N.mem i U.domain) (h : R.IsCut i cut) : cut = i := by
  apply N.ext
  intro z
  exact (h z).trans (by rw [spec, relation]; exact ⟨And.right,fun hz => ⟨U.ordered.transitive i hi z hz,hz⟩⟩)

private theorem candidate_in {bounds i f y h stage : V}
    (function : Internal.FunctionOn N.mem bounds U.domain)
    (atHeight : Internal.At N.mem bounds i h) (rank : N.Rank h stage)
    (candidate : U.Candidate U.key bounds i f y) : N.mem y stage := by
  obtain ⟨other,v,atOther,rank',member,_⟩ := candidate
  obtain ⟨_,_,one⟩ := function.1 i (SetRecursion.at_domain function atHeight)
  have eq := (one other atOther).trans (one h atHeight).symm
  subst other
  exact (N.rank_unique rank' rank) ▸ member

set_option maxHeartbeats 1600000 in
/-- Set-length dependent recursion for a definable total class
relation. A first recursion bounds the output ranks, then a set
wellorder chooses outputs within those bounds. -/
theorem class_recursion_exists {w : V} (omega : Internal.Omega N.mem w) (regular : N.Regular) :
    ∃ graph, Internal.FunctionOn N.mem graph U.domain ∧
      ∀ i, N.mem i U.domain → ∃ prior value, N.Restricts graph i prior ∧
        Internal.At N.mem graph i value ∧ U.choices U.key i prior value := by
  let budget := U.boundsRecursor omega regular
  obtain ⟨bounds, enveloped⟩ := budget.solution_exists
  have ordinals {i h : V} (edge : Internal.At N.mem bounds i h) : N.Ordinal h := by
    have inside := SetRecursion.at_domain enveloped.functionOn edge
    obtain ⟨_,_,value,_,_,stored,cases_⟩ := enveloped.agrees i inside
    obtain ⟨_,_,unique⟩ := enveloped.functionOn.1 i inside
    have same := (unique value stored).trans (unique h edge).symm
    subst value
    exact U.boundStep_ordinal (i := i) cases_
  let sup := N.union (N.range bounds)
  have supOrd : N.Ordinal sup := N.ordinal_union _ fun h membership => by
    obtain ⟨i,edge⟩ := (N.mem_range _ _).mp membership
    exact ordinals edge
  obtain ⟨ambient,ambientRank⟩ := N.rank_exists supOrd
  obtain ⟨order,wellorder⟩ := N.wellOrdering ambient
  let selector : Selector (N := N) := {
    bounds := bounds
    order := order
    ambient := ambient
    wellOrder := wellorder
    within := fun i h s edge rank => N.rank_subset rank ambientRank fun a ha =>
      (N.mem_union _ _).mpr ⟨h,(N.mem_range _ _).mpr ⟨i,edge⟩,ha⟩
  }
  let machine := U.choosingRecursor selector
  obtain ⟨graph, computed⟩ := machine.solution_exists
  have justified (i : V) (hi : N.mem i U.domain)
      (earlier : ∀ j, N.mem j i → ∀ h s y, Internal.At N.mem bounds j h → N.Rank h s →
        Internal.At N.mem graph j y → N.mem y s) :
      ∃ prior, N.Restricts graph i prior ∧
        ∀ y, Internal.At N.mem graph i y → U.Candidate U.key bounds i prior y := by
    obtain ⟨cut, history, nextHeight, domain, sub, atHeight, boundStep⟩ := enveloped.agrees i hi
    have sameCut : cut = i := U.cut_value rfl rfl hi domain
    subst cut
    let height := N.union (N.range history)
    have hOrd : N.Ordinal height := N.ordinal_union _ (fun a membership => by
      obtain ⟨j,h⟩ := (N.mem_range _ _).mp membership
      exact ordinals ((N.restricts_value sub).mp h).2)
    obtain ⟨stage, earlierRank⟩ := N.rank_exists hOrd
    have supRank : N.SupRank history stage :=
      ⟨N.range history,height,N.mem_range history,N.mem_union (N.range history),earlierRank⟩
    obtain ⟨key, dom, pair, cases_⟩ := boundStep
    have read : Internal.OrderedPair N.mem U.key U.domain budget.updateKey := N.orderedPair_intro _ _
    obtain ⟨same, so⟩ := Internal.orderedPair_injective pair read
    subst key
    subst dom
    have covered : U.LeastBound U.key U.domain stage nextHeight := by
      rcases cases_ with ⟨s,rank,bound⟩ | ⟨no,zero⟩
      · exact N.supRank_unique rank supRank ▸ bound
      · exact (no ⟨stage,supRank⟩).elim
    obtain ⟨out,outRank,outputCovers⟩ := covered.1
    obtain ⟨cut, prior, value, actual, restr, atValue, update⟩ := computed.agrees i hi
    have cutEq : cut = i := U.cut_value rfl rfl hi actual
    subst cut
    have typedGraph : N.RelationBetween prior U.domain stage := by
      intro p pn
      obtain ⟨whole, j, hj, y, code⟩ := (restr p).mp pn
      have atOutput : Internal.At N.mem graph j y := ⟨p,whole,code⟩
      have jIn := U.ordered.transitive i hi j hj
      obtain ⟨beta, jBound, _⟩ := enveloped.functionOn.1 j jIn
      obtain ⟨src, curRank⟩ := N.rank_exists (ordinals jBound)
      have lives := earlier j hj beta src y jBound curRank atOutput
      have betaIn : N.mem beta (N.range history) := (N.mem_range _ _).mpr
        ⟨j,(N.restricts_value sub).mpr ⟨hj,jBound⟩⟩
      have subRank : N.Subset beta height := fun v hv =>
        (N.mem_union _ _).mpr ⟨beta,betaIn,hv⟩
      exact ⟨j,y,jIn,N.rank_subset curRank earlierRank subRank y lives,code⟩
    obtain ⟨v, inside, choice⟩ := outputCovers i hi prior typedGraph
    have candidate : U.Candidate U.key bounds i prior v := ⟨nextHeight,out,atHeight,outRank,inside,choice⟩
    have correct : U.Candidate U.key bounds i prior value :=
      chooseStep_correct (U := U) selector update ⟨v,candidate⟩
    refine ⟨prior,restr,fun y edge => ?_⟩
    obtain ⟨_,_,one⟩ := computed.functionOn.1 i hi
    exact ((one value atValue).trans (one y edge).symm) ▸ correct
  have heightAt := Definable.graphValue (N := N) (n := 7) (i := 5) (j := 3) (k := 2)
    (by decide) (by decide) (by decide)
  have rank := Definable.rank (N := N) (n := 7) (i := 2) (j := 1) (by decide) (by decide)
  have output := Definable.graphValue (N := N) (n := 7) (i := 6) (j := 3) (k := 0)
    (by decide) (by decide) (by decide)
  have member := Definable.mem (N := N) (n := 7) (i := 0) (j := 1) (by decide) (by decide)
  have described := Definable.all (Definable.all (Definable.all
    (heightAt.implies (rank.implies (output.implies member)))))
  have bounded : ∀ i, N.mem i U.domain → ∀ h s y, Internal.At N.mem bounds i h → N.Rank h s →
      Internal.At N.mem graph i y → N.mem y s := by
    apply N.order_induction U.ordered.ordered [bounds,graph] described
    intro i inD previous h s y atHeight ranked atValue
    obtain ⟨prior,_,correct⟩ := justified i inD
      (fun j earlier => previous j (U.ordered.transitive i inD j earlier) earlier)
    exact U.candidate_in enveloped.functionOn atHeight ranked (correct y atValue)
  refine ⟨graph,computed.functionOn,fun i hi => ?_⟩
  obtain ⟨prior,restr,proof⟩ := justified i hi
    (fun j earlier => bounded j (U.ordered.transitive i hi j earlier))
  obtain ⟨v,atV,_⟩ := computed.functionOn.1 i hi
  obtain ⟨_,_,_,_,_,choice⟩ := proof v atV
  exact ⟨prior,v,restr,atV,choice⟩

end PalomarI3380.SquareRepresentation.SetContext.ClassUpdate
