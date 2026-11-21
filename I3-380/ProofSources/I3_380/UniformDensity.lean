module
public import I3_380.DenseClassFamily
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

theorem close_log {base domain cut graph prior : V}
    (baseValid : N.OrderCondition base) (order : N.Ordinal cut) (sub : N.Subset cut domain)
    (function : Internal.FunctionOn N.mem graph domain) (restricted : N.Restricts graph cut prior)
    (history : ∀ i, N.mem i cut → ∀ p, Internal.At N.mem graph i p →
      N.Refines p base ∧ ∀ j, N.mem j i → ∀ q, Internal.At N.mem graph j q → N.Refines p q) :
    ∃ q, N.Refines q base ∧ ∀ i p, Internal.At N.mem prior i p → N.Refines q p := by
  classical
  let family := N.range prior
  by_cases some : N.NonemptySet family
  · have valid (p : V) (hp : N.mem p family) : N.OrderCondition p := by
      obtain ⟨i,link⟩ := (N.mem_range _ _).mp hp
      obtain ⟨inCut,value⟩ := (N.restricts_value restricted).mp link
      exact N.refines_strong (history i inCut p value).1
    have chain (p q : V) (hp : N.mem p family) (hq : N.mem q family) :
        N.Refines p q ∨ N.Refines q p := by
      obtain ⟨i,atP⟩ := (N.mem_range _ _).mp hp
      obtain ⟨j,atQ⟩ := (N.mem_range _ _).mp hq
      obtain ⟨hi,pKnown⟩ := (N.restricts_value restricted).mp atP
      obtain ⟨hj,qKnown⟩ := (N.restricts_value restricted).mp atQ
      rcases order.ordered.compare i j hi hj with before | same | after
      · exact Or.inr ((history j hj q qKnown).2 i before p pKnown)
      · subst j
        obtain ⟨_,_,one⟩ := function.1 i (sub i hi)
        have eq := (one p pKnown).trans (one q qKnown).symm
        subst q
        exact Or.inl (N.refines_refl (valid p hp))
      · exact Or.inl ((history i hi p pKnown).2 j after q qKnown)
    obtain ⟨q,_,_,_,_,below⟩ := N.close_order_conditions family valid chain
    obtain ⟨p,hp⟩ := some
    obtain ⟨i,atP⟩ := (N.mem_range _ _).mp hp
    obtain ⟨inCut,original⟩ := (N.restricts_value restricted).mp atP
    exact ⟨q,N.refines_trans (below p hp) (history i inCut p original).1,fun n r h =>
      below r ((N.mem_range _ _).mpr ⟨n,h⟩)⟩
  · exact ⟨base,N.refines_refl baseValid,fun i p h => (some ⟨p,(N.mem_range _ _).mpr ⟨i,h⟩⟩).elim⟩

variable {R : V → V → V → Prop}

private theorem goodIndex_def (definition : Definable.Relation3 N R)
    {n i g e b k : Nat} (hi : i < n) (hg : g < n) (he : e < n) (hb : b < n) (hk : k < n) :
    N.square.Definable n (fun env => ∀ q, Internal.At N.mem (env g) (env i) q →
      N.Refines q (env b) ∧
      (∃ x, Internal.At N.mem (env e) (env i) x ∧ R (env k) x q) ∧
      ∀ j, N.mem j (env i) → ∀ p, Internal.At N.mem (env g) j p → N.Refines q p) := by
  have out := Definable.graphValue (N := N) (n := n+1) (i := g+1) (j := i+1) (k := 0)
    (by omega) (by omega) (by omega)
  have earlier := N.refines_def (n := n+1) (p := 0) (q := b+1) (by omega) (by omega)
  have value := Definable.graphValue (N := N) (n := n+2) (i := e+2) (j := i+2) (k := 0)
    (by omega) (by omega) (by omega)
  have expected := definition (n := n+2) (i := k+2) (j := 0) (k := 1) (by omega) (by omega) (by omega)
  have old := Definable.graphValue (N := N) (n := n+3) (i := g+3) (j := 1) (k := 0)
    (by omega) (by omega) (by omega)
  have stronger := N.refines_def (n := n+3) (p := 2) (q := 0) (by omega) (by omega)
  have history := Definable.boundedAll (i := i+1) (by omega) _ (Definable.all (old.implies stronger))
  exact Definable.all (out.implies (earlier.and ((Definable.ex (value.and expected)).and history)))

set_option maxHeartbeats 1700000 in
/-- A set-indexed family of monotone dense requirements is dense
simultaneously. The recursion is set-coded in the membership model. -/
theorem meet_family {w base key source : V} (omega : Internal.Omega N.mem w) (regular : N.Regular)
    (definition : Definable.Relation3 N R) (baseValid : N.OrderCondition base)
    (dense : ∀ x, N.mem x source → ∀ p, N.OrderCondition p → ∃ q, N.Refines q p ∧ R key x q)
    (monotone : ∀ x p q, N.Refines q p → R key x p → R key x q) :
    ∃ q, N.Refines q base ∧ ∀ x, N.mem x source → R key x q := by
  obtain ⟨domain,enumeration,domainOrd,enumOn,onto⟩ := N.ordinal_enumeration source
  let action : ClassUpdate N := {
    domain := domain
    ordered := domainOrd
    key := N.triple key base enumeration
    choices := N.MeetStep R
    definable := N.meetStep_def definition
    total := fun i _ prior => N.meetStep_total (R := R) key base enumeration i prior
  }
  obtain ⟨graph,function,step⟩ := action.class_recursion_exists omega regular
  have defn := N.goodIndex_def definition (n := 6) (i := 0) (g := 2) (e := 3) (b := 4) (k := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have known : ∀ i, N.mem i domain → ∀ p, Internal.At N.mem graph i p →
      N.Refines p base ∧
      (∃ x, Internal.At N.mem enumeration i x ∧ R key x p) ∧
      ∀ j, N.mem j i → ∀ q, Internal.At N.mem graph j q → N.Refines p q := by
    apply N.order_induction domainOrd.ordered [graph,enumeration,base,key] defn
    intro i inside ih p hp
    obtain ⟨prior,value,restriction,atValue,actionTaken⟩ := step i inside
    obtain ⟨_,_,one⟩ := function.1 i inside
    have same := (one value atValue).trans (one p hp).symm
    subst value
    have subset : N.Subset i domain := domainOrd.transitive i inside
    obtain ⟨bounded,extendsBase,extendsPrior⟩ := N.close_log baseValid (domainOrd.of_mem N inside)
      subset function restriction (fun j hj q hq =>
        let previous := ih j (subset j hj) hj q hq; ⟨previous.1,previous.2.2⟩)
    obtain ⟨x, sourceX, _⟩ := enumOn.1 i inside
    have xIn := (onto x).mpr ⟨i,sourceX⟩
    obtain ⟨q, extendsBound, settled⟩ := dense x xIn bounded (N.refines_strong extendsBase)
    have possible : ∃ q, N.Request R key base enumeration i prior q :=
      ⟨q,N.refines_trans extendsBound extendsBase,⟨x,sourceX,settled⟩,fun j r h =>
        N.refines_trans extendsBound (extendsPrior j r h)⟩
    have fixed := N.meetStep_valid actionTaken possible
    exact ⟨fixed.1,fixed.2.1,fun j hj r hr => fixed.2.2 j r ((N.restricts_value restriction).mpr ⟨hj,hr⟩)⟩
  let prior := N.restrictGraph graph domain
  have restriction := N.restricts_canonical graph domain
  obtain ⟨q,extendsBase,extendsAll⟩ := N.close_log baseValid domainOrd (N.subset_refl _) function
    restriction (fun i hi p hp => let current := known i hi p hp; ⟨current.1,current.2.2⟩)
  refine ⟨q,extendsBase,fun x hx => ?_⟩
  obtain ⟨i, lookup⟩ := (onto x).mp hx
  have iIn := SetRecursion.at_domain enumOn lookup
  obtain ⟨p, read, _⟩ := function.1 i iIn
  obtain ⟨y, atY, reply⟩ := (known i iIn p read).2.1
  obtain ⟨_,_,one⟩ := enumOn.1 i iIn
  have same := (one y atY).trans (one x lookup).symm
  subst y
  exact monotone x p q (extendsAll i p ((N.restricts_value restriction).mpr ⟨iIn,read⟩)) reply

end PalomarI3380.SquareRepresentation.SetContext
