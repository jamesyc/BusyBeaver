module
public import I3_334Support.SetTheory.ExpandedZFC
@[expose] public section

namespace PalomarI3380.Logic.Expanded

variable {V : Type}

/-- The global order has minima on nonempty definable classes. Minima of
arbitrary external subsets of a nonstandard model are not required. -/
structure ClassMinimum (E G : V → V → Prop) : Prop where
  asymmetric : ∀ x y, G x y → ¬ G y x
  least : ∀ r, Binary E G r → ∀ x, (∃ y, r x y) →
    ∃ y, r x y ∧ ∀ z, r x z → y = z ∨ G y z

namespace Binary

variable {E G : V → V → Prop} {r : V → V → Prop}

def leastRelation (G r : V → V → Prop) (x y : V) : Prop :=
  r x y ∧ ∀ z, r x z → y = z ∨ G y z

theorem least_def (described : Binary E G r) : Binary E G (leastRelation G r) := by
  let rel : ClassRelation E G := ⟨r,described⟩
  let x := Argument.variable (V := V) 0
  let y := Argument.variable (V := V) 1
  let z := Argument.variable (V := V) 2
  let body : Formula V := .all (.imp (rel.reference y x)
    (.or (.eq z x) (.order z x)))
  have scope : Bound (rel.reference x y) 2 := rel.reference_bound (Nat.zero_lt_succ 1)
    (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
  have bodyScope : Bound body 2 := by
    refine ⟨rel.reference_bound (Nat.succ_lt_succ (Nat.zero_lt_succ 1)) (Nat.zero_lt_succ 2),?_⟩
    simp [Bound,Argument.bound,x,z]
  refine ⟨.and (rel.reference x y) body,⟨scope,bodyScope⟩,fun env => ?_⟩
  refine and_congr (rel.reference_eval _ _ _) ?_
  apply forall_congr'
  intro v
  exact imp_congr (rel.reference_eval _ _ _) Iff.rfl

theorem least_functional (minimum : ClassMinimum E G) {a b c : V}
    (left : leastRelation G r a b) (right : leastRelation G r a c) : b = c := by
  rcases left.2 c right.1 with same | order
  · exact same
  · rcases right.2 b left.1 with same | reverse
    · exact same.symm
    · exact (minimum.asymmetric b c order reverse).elim

end Binary
end PalomarI3380.Logic.Expanded

namespace PalomarI3380.SquareRepresentation.SetContext.OrdinaryContext

open Logic Expanded
variable {V : Type} {E : V → V → Prop} (h : ZFCModel E) (inh : Nonempty V)

local notation "K" => underlying h inh

theorem generic_minimum (L : (K).OrderForcingLanguage) (G : GenericOrder K)
    {w : V} (omega : Internal.Omega E w) (regular : (K).Regular) :
    ClassMinimum E G.order := by
  let N := underlying h inh
  refine ⟨?_,?_⟩
  · rintro x y ⟨p,pIn,xy⟩ ⟨q,qIn,yx⟩
    obtain ⟨r,rIn,fromP,fromQ⟩ := G.directed p q pIn qIn
    obtain ⟨a,s,edge,valid,xIn,yIn,connected⟩ := N.orderEdge_larger fromP xy
    have other := (N.orderEdge_at valid yIn xIn).mp (N.orderEdge_larger fromQ yx)
    exact WellOrderOn.asymm N valid.order xIn yIn connected other
  · intro r described x inhabited
    obtain ⟨y,hy⟩ := inhabited
    obtain ⟨p,pIn,a,s,relation,valid,containsY⟩ := G.covers L omega regular y
    obtain ⟨subset,spec⟩ := generic_separation h inh L G omega regular described.converse s x
    have sub : N.Subset subset s := fun z hz => ((spec z).mp hz).1
    obtain ⟨z,hz,least⟩ := valid.order.least subset sub ⟨y,(spec y).mpr ⟨containsY,hy⟩⟩
    obtain ⟨zIn,zWitness⟩ := (spec z).mp hz
    refine ⟨z,zWitness,fun t ht => ?_⟩
    classical
    by_cases inner : E t s
    · exact (least t ((spec t).mpr ⟨inner,ht⟩)).elim Or.inl
        (fun e => Or.inr ((G.order_agrees pIn valid zIn inner).mpr e))
    · obtain ⟨q,qIn,cover⟩ := G.covers L omega regular t
      obtain ⟨p',p'In,toP,toQ⟩ := G.directed p q pIn qIn
      obtain ⟨b,larger,g,cond,tIn⟩ := N.covers_larger toQ cover
      have extension := N.refines_transport valid cond toP
      have zThere := N.rank_subset valid.ranked cond.ranked extension.height z zIn
      exact Or.inr ⟨p',p'In,b,larger,g,cond,zThere,tIn,extension.initial z zIn t tIn inner⟩

include h inh in
/-- A countable membership model has an expansion by a global order
admitting definable minima and expanded Separation and Replacement.
The membership structure remains the original model. -/
theorem amenable_global_order (enumerated : Listing V) :
    ∃ G : V → V → Prop, ClassAxioms E G ∧ ClassMinimum E G := by
  let env := fun _ : Nat => Classical.choice inh
  obtain ⟨w,omega⟩ := h.omega env
  have regular : (K).Regular := fun set nonempty => h.foundation env set nonempty
  obtain ⟨L⟩ := forcing_language_exists h inh
  obtain ⟨G⟩ := (K).generic_exists enumerated
  exact ⟨G.order,generic_class_axioms h inh L G omega regular,generic_minimum h inh L G omega regular⟩

end PalomarI3380.SquareRepresentation.SetContext.OrdinaryContext
