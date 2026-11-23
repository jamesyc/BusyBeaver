module
public import I3_334Support.SetTheory.Forcing.ForcingTranslation
public import I3_334Support.Logic.FormulaListing
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic Expanded
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

def Dense (class_ : V → Prop) : Prop :=
  ∀ p, N.OrderCondition p → ∃ q, N.Refines q p ∧ class_ q

def GroundUnary (class_ : V → Prop) : Prop :=
  ∃ formula : Expanded.Formula V, Expanded.Bound formula 1 ∧
    ∀ env, Expanded.eval N.mem (fun _ _ => False) formula env ↔ class_ (env 0)

structure GenericOrder (N : SetContext M V) where
  filter : V → Prop
  inhabited : ∃ p, filter p
  conditions : ∀ p, filter p → N.OrderCondition p
  directed : ∀ p q, filter p → filter q → ∃ r, filter r ∧ N.Refines r p ∧ N.Refines r q
  meets : ∀ pred, N.GroundUnary pred → N.Dense pred → ∃ p, filter p ∧ pred p

def ReadClass (formula : Expanded.Formula V) (x : V) : Prop :=
  Expanded.eval N.mem (fun _ _ => False) formula (fun _ => x)

noncomputable def meetNext (listing : Listing V) (n : Nat) (p : {p : V // N.OrderCondition p}) :
    {q : V // N.OrderCondition q} := by
  classical
  let goal := N.ReadClass (listing.formulas.get n)
  exact if dense : N.Dense goal then
    ⟨Classical.choose (dense p.val p.property), N.refines_strong (Classical.choose_spec (dense p.val p.property)).1⟩
    else p

theorem meetNext_refines (listing : Listing V) (n : Nat) (p : {p : V // N.OrderCondition p}) :
    N.Refines (N.meetNext listing n p).val p.val := by
  unfold meetNext
  dsimp only
  split
  · rename_i dense
    exact (Classical.choose_spec (dense p.val p.property)).1
  · exact N.refines_refl p.property

theorem meetNext_member (listing : Listing V) (n : Nat) (p : {p : V // N.OrderCondition p})
    (h : N.Dense (N.ReadClass (listing.formulas.get n))) :
    N.ReadClass (listing.formulas.get n) (N.meetNext listing n p).val := by
  unfold meetNext
  dsimp only
  rw [dite_eq_left h]
  exact (Classical.choose_spec (h p.val p.property)).2

noncomputable def genericChain (listing : Listing V) (first : {p : V // N.OrderCondition p}) :
    Nat → {q : V // N.OrderCondition q}
  | 0 => first
  | n+1 => N.meetNext listing n (genericChain listing first n)

theorem chain_refines (listing : Listing V) (first : {p : V // N.OrderCondition p})
    {i j : Nat} (h : i ≤ j) :
    N.Refines (N.genericChain listing first j).val (N.genericChain listing first i).val := by
  induction j with
  | zero =>
    have eq : i = 0 := by omega
    subst i
    exact N.refines_refl first.property
  | succ j ih =>
    by_cases equal : i = j + 1
    · subst i
      exact N.refines_refl (N.genericChain listing first (j+1)).property
    · have step := N.meetNext_refines listing j (N.genericChain listing first j)
      exact N.refines_trans step (ih (by omega))

/-- A countable base model admits a filter meeting every base-definable
dense class, including instances with arbitrary point parameters. -/
theorem generic_exists (listing : Listing V) : Nonempty (GenericOrder N) := by
  obtain ⟨p, hp⟩ := N.empty_rankOrder
  let first : {p : V // N.OrderCondition p} := ⟨p,hp⟩
  let path := N.genericChain listing first
  let filter := fun p => ∃ n, N.Refines (path n).val p
  refine ⟨⟨filter,⟨p,0,N.refines_refl hp⟩,?_,?_,?_⟩⟩
  · rintro q ⟨n,h⟩
    exact N.refines_weak h
  · rintro p q ⟨i,hp⟩ ⟨j,hq⟩
    let k := max i j
    refine ⟨(path k).val,⟨k,N.refines_refl (path k).property⟩,?_,?_⟩
    · exact N.refines_trans (N.chain_refines listing first (Nat.le_max_left _ _)) hp
    · exact N.refines_trans (N.chain_refines listing first (Nat.le_max_right _ _)) hq
  · intro pred description dense
    obtain ⟨formula,scope,specifies⟩ := description
    obtain ⟨i, hi⟩ := listing.formulas.contains formula
    have agrees (x : V) : N.ReadClass (listing.formulas.get i) x ↔ pred x := by
      rw [hi]
      exact specifies (fun _ => x)
    have actual : N.Dense (N.ReadClass (listing.formulas.get i)) := fun q hq => by
      obtain ⟨r, extends_, works⟩ := dense q hq
      exact ⟨r,extends_,(agrees r).mpr works⟩
    exact ⟨(path (i+1)).val,⟨i+1,N.refines_refl (path (i+1)).property⟩,
      (agrees _).mp (N.meetNext_member listing i (path i) actual)⟩

namespace GenericOrder

variable {N : SetContext M V} (G : GenericOrder N)

def order (x y : V) : Prop := ∃ p, G.filter p ∧ N.OrderEdge p x y

theorem covers (L : N.OrderForcingLanguage) {w : V} (omega : Internal.Omega N.mem w)
    (regular : N.Regular) (x : V) : ∃ p, G.filter p ∧ N.Covers p x :=
  G.meets (fun _p => N.Covers _p x)
    ⟨L.coverTest (.variable 0) (.named x), L.coverTest_scope (Nat.zero_lt_succ 0) trivial,
      fun env => L.coverTest_eval _ _ env⟩
    (fun _p hp => N.orders_cover omega regular hp x)

theorem order_agrees {p a s r x y : V} (onPath : G.filter p)
    (condition : N.RankOrder p a s r) (hx : N.mem x s) (hy : N.mem y s) :
    G.order x y ↔ Internal.At N.mem r x y := by
  constructor
  · rintro ⟨q,qIn,edge⟩
    obtain ⟨u,uIn,up,uq⟩ := G.directed p q onPath qIn
    obtain ⟨b,t,g,h⟩ := G.conditions u uIn
    have extension := N.refines_transport condition h up
    have sub := N.rank_subset condition.ranked h.ranked extension.height
    have inner := (N.orderEdge_at h (sub x hx) (sub y hy)).mp (N.orderEdge_larger uq edge)
    exact (extension.agrees x hx y hy).mpr inner
  · exact fun h => ⟨p,onPath,(N.orderEdge_at condition hx hy).mpr h⟩

end GenericOrder
end PalomarI3380.SquareRepresentation.SetContext
