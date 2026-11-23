module
public import I3_334Support.SetTheory.Forcing.OrderForcingFormulas
@[expose] public section

namespace PalomarI3380.Logic.Expanded

variable {V : Type}

/-- A classical presentation using conjunction, negation and existential
binding. These are the three forcing clauses used below. -/
inductive Fragment (V : Type) where
  | bot
  | eq (a b : Argument V)
  | mem (a b : Argument V)
  | order (a b : Argument V)
  | and (a b : Fragment V)
  | neg (body : Fragment V)
  | ex (body : Fragment V)

def Fragment.bound : Fragment V → Nat → Prop
  | .bot, _ => True
  | .eq x y,n | .mem x y,n | .order x y,n => x.bound n ∧ y.bound n
  | .and f g,n => f.bound n ∧ g.bound n
  | .neg f,n => f.bound n
  | .ex f,n => f.bound (n+1)

def Fragment.eval (E G : V → V → Prop) : Fragment V → (Nat → V) → Prop
  | .bot, _ => False
  | .eq a b,s => a.value s = b.value s
  | .mem a b,s => E (a.value s) (b.value s)
  | .order a b,s => G (a.value s) (b.value s)
  | .and a b,s => a.eval E G s ∧ b.eval E G s
  | .neg a,s => ¬a.eval E G s
  | .ex a,s => ∃ x, a.eval E G (pushValue s x)

def Formula.fragment : Formula V → Fragment V
  | .bot => .bot
  | .eq a b => .eq a b
  | .mem a b => .mem a b
  | .order a b => .order a b
  | .and a b => .and a.fragment b.fragment
  | .or a b => .neg (.and (.neg a.fragment) (.neg b.fragment))
  | .imp a b => .neg (.and a.fragment (.neg b.fragment))
  | .all f => .neg (.ex (.neg f.fragment))
  | .ex f => .ex f.fragment

theorem fragment_scope (p : Formula V) {n : Nat} (h : Bound p n) : p.fragment.bound n := by
  induction p generalizing n with
  | bot | eq | mem | order => exact h
  | and a b ia ib | or a b ia ib | imp a b ia ib => exact ⟨ia h.1,ib h.2⟩
  | all p i | ex p i => exact i h

theorem fragment_eval (E G : V → V → Prop) (p : Formula V) (env : Nat → V) :
    p.fragment.eval E G env ↔ eval E G p env := by
  classical
  induction p generalizing env with
  | bot | eq | mem | order => rfl
  | and a b ia ib => exact and_congr (ia env) (ib env)
  | or a b ia ib =>
    simp only [Formula.fragment,Fragment.eval,eval,ia,ib]
    exact ⟨fun h => Classical.byContradiction fun no => h ⟨fun ha => no (Or.inl ha),fun hb => no (Or.inr hb)⟩,
      fun h no => h.elim no.1 no.2⟩
  | imp a b ia ib =>
    simp only [Formula.fragment,Fragment.eval,eval,ia,ib]
    exact ⟨fun h ha => Classical.byContradiction fun no => h ⟨ha,no⟩,fun h h' => h'.2 (h h'.1)⟩
  | all p ih =>
    simp only [Formula.fragment,Fragment.eval,eval,ih]
    exact ⟨fun h x => Classical.byContradiction fun no => h ⟨x,no⟩,
      fun h ⟨x,no⟩ => no (h x)⟩
  | ex p ih => exact exists_congr fun x => ih (pushValue env x)

end PalomarI3380.Logic.Expanded

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic Expanded

variable {A V : Type} {M : Algebra A} (N : SetContext M V)

def Forces : Fragment V → V → (Nat → V) → Prop
  | .bot, _, _ => False
  | .eq a b, _, s => a.value s = b.value s
  | .mem a b, _, s => N.mem (a.value s) (b.value s)
  | .order a b, p, s => N.OrderEdge p (a.value s) (b.value s)
  | .and a b, p, s => Forces a p s ∧ Forces b p s
  | .neg a, p, s => ∀ q, N.Refines q p → ¬Forces a q s
  | .ex a, p, s => ∀ q, N.Refines q p → ∃ r, N.Refines r q ∧ ∃ x, Forces a r (pushValue s x)

theorem force_refines (formula : Fragment V) {p q : V} (stronger : N.Refines q p) (env : Nat → V)
    (h : N.Forces formula p env) : N.Forces formula q env := by
  induction formula generalizing p q env with
  | bot | eq | mem => exact h
  | order => exact N.orderEdge_larger stronger h
  | and a b ia ib => exact ⟨ia stronger env h.1,ib stronger env h.2⟩
  | neg _ _ => exact fun r hr => h r (N.refines_trans hr stronger)
  | ex _ _ => exact fun r hr => h r (N.refines_trans hr stronger)

/-- Formula codes for the forcing order in the underlying membership
language. An expanded predicate is never evaluated in these codes. -/
structure OrderForcingLanguage (N : SetContext M V) where
  refines : Expanded.Formula V
  refines_scope : Expanded.Bound refines 2
  refines_eval : ∀ env, Expanded.eval N.mem (fun _ _ => False) refines env ↔ N.Refines (env 0) (env 1)
  edge : Expanded.Formula V
  edge_scope : Expanded.Bound edge 3
  edge_eval : ∀ env, Expanded.eval N.mem (fun _ _ => False) edge env ↔ N.OrderEdge (env 0) (env 1) (env 2)
  covers : Expanded.Formula V
  covers_scope : Expanded.Bound covers 2
  covers_eval : ∀ env, Expanded.eval N.mem (fun _ _ => False) covers env ↔ N.Covers (env 0) (env 1)

end PalomarI3380.SquareRepresentation.SetContext
