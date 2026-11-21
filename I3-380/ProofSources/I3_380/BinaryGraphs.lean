module
public import I3_380.ModelSyntax
public import I3_380.RegularRanks
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

private def pairSlots : Nat → Nat
  | 0 => 1
  | 1 => 0
  | k + 2 => k + 6

private theorem pairs_scope (length i : Nat) (limit : i < length + 2) : pairSlots i < length + 6 := by
  cases i with
  | zero => simp [pairSlots]
  | succ j =>
    cases j with
    | zero => simp [pairSlots]
    | succ j =>
      change j + 6 < length + 6
      omega

private theorem pairs_env (params : List V) (a b p x y : V) :
    pushValue (pushValue (parameterEnv (a :: b :: params) p a) x) y ∘ pairSlots =
      fun i => match i with
        | 0 => x
        | 1 => y
        | k + 2 => params[k]?.getD p := by
  funext i
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

/-- Separation on a common pair bound produces the actual graph of a
definable binary relation between two sets. -/
theorem binary_graph (params : List V) {R : (Nat → V) → Prop}
    (definable : N.square.Definable (params.length + 2) R) (a b : V) :
    ∃ f, (∀ x y, Internal.At N.mem f x y ↔ N.mem x a ∧ N.mem y b ∧ R (parameterEnv params x y)) ∧
      (∀ p, N.mem p f → ∃ x y, N.mem x a ∧ N.mem y b ∧ R (parameterEnv params x y) ∧
        Internal.OrderedPair N.mem x y p) := by
  let arity := params.length + 6
  have left := Definable.mem (N := N) (n := arity) (i := 1) (j := 4) (by dsimp [arity]; omega) (by dsimp [arity]; omega)
  have right := Definable.mem (N := N) (n := arity) (i := 0) (j := 5) (by dsimp [arity]; omega) (by dsimp [arity]; omega)
  have bound := Definable.orderedPair (N := N) (n := arity) (i := 1) (j := 0) (k := 2)
    (by dsimp [arity]; omega) (by dsimp [arity]; omega) (by dsimp [arity]; omega)
  have predicate := Definable.ex (Definable.ex (left.and (right.and
    ((definable.reindex (m := arity) pairSlots (pairs_scope params.length)).and bound))))
  obtain ⟨f, represented⟩ := N.separate (a :: b :: params) predicate (N.PairBound a b) a
  have agree (p x y : V) :
      R (pushValue (pushValue (parameterEnv (a :: b :: params) p a) x) y ∘ pairSlots) ↔
        R (parameterEnv params x y) := by
    obtain ⟨form,scope,describes⟩ := definable
    refine (describes _).symm.trans ((RelationFormula.eval_congr form scope _ _ ?_).trans (describes _))
    rw [pairs_env]
    intro i small
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ k =>
        have fitted : k < params.length := by omega
        change params[k]?.getD p = params[k]?.getD x
        rw [List.getElem?_eq_getElem fitted]
        rfl
  have built (p : V) :
      N.mem p f ↔ ∃ x y, N.mem x a ∧ N.mem y b ∧ R (parameterEnv params x y) ∧
        Internal.OrderedPair N.mem x y p := by
    rw [represented]
    constructor
    · rintro ⟨_,x,y,xa,yb,related,code⟩
      exact ⟨x,y,xa,yb,(agree p x y).mp related,code⟩
    · rintro ⟨x,y,xa,yb,related,code⟩
      have equal := (N.orderedPair_iff x y p).mp code
      exact ⟨equal.symm ▸ N.in_pairBound xa yb,x,y,xa,yb,(agree p x y).mpr related,code⟩
  refine ⟨f,fun x y => (N.at_pair _ _ _).trans ((built _).trans ?_), fun p => (built p).mp⟩
  constructor
  · rintro ⟨u,v,hu,hv,edges,h⟩
    obtain ⟨same, also⟩ := Internal.orderedPair_injective h (N.orderedPair_intro x y)
    subst u
    subst v
    exact ⟨hu,hv,edges⟩
  · exact fun ⟨hx,hy,edge⟩ => ⟨x,y,hx,hy,edge,N.orderedPair_intro x y⟩

end PalomarI3380.SquareRepresentation.SetContext
