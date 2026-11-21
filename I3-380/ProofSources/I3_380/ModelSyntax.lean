module
public import I3_380.Logic.SatisfactionSemantics
public import I3_380.OmegaSets
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

noncomputable def numeral : Nat → V
  | 0 => N.empty
  | n + 1 => N.succ (numeral n)

theorem numeral_def (n : Nat) (x : V) :
    Internal.Numeral N.mem n x ↔ x = N.numeral n := by
  induction n generalizing x with
  | zero => exact N.empty_unique x
  | succ n ih =>
    change (∃ y, Internal.Numeral N.mem n y ∧ Internal.Succ N.mem y x) ↔ x = N.succ (N.numeral n)
    constructor
    · rintro ⟨y, hy, next⟩
      have same := (ih y).mp hy
      subst y
      exact (N.internal_succ _ _).mp next
    · rintro rfl
      exact ⟨N.numeral n, (ih _).mpr rfl, N.mem_succ _⟩

theorem numeral_in_omega {w : V} (hw : Internal.Omega N.mem w) (n : Nat) : N.mem (N.numeral n) w := by
  induction n with
  | zero =>
    obtain ⟨z, hz, has⟩ := hw.1.1
    change N.mem N.empty w
    exact ((N.empty_unique _).mp hz) ▸ has
  | succ n ih =>
    obtain ⟨x, successor, atX⟩ := hw.1.2 (N.numeral n) ih
    change N.mem (N.succ (N.numeral n)) w
    exact ((N.internal_succ _ _).mp successor) ▸ atX

theorem numeral_injective : Function.Injective N.numeral := by
  have ordinal (n : Nat) : N.Ordinal (N.numeral n) := by
    induction n with
    | zero => exact N.ordinal_empty
    | succ n ih => exact N.ordinal_succ ih
  have order (a b : Nat) (h : a < b) : N.mem (N.numeral a) (N.numeral b) := by
    induction b with
    | zero => omega
    | succ b ih =>
      apply (N.mem_succ _ _).mpr
      by_cases same : a = b
      · exact Or.inr (congrArg N.numeral same)
      · exact Or.inl (ih (by omega))
  intro a b eq
  rcases Nat.lt_trichotomy a b with before | equal | after
  · exact ((ordinal b).not_mem_self N (eq ▸ order a b before)).elim
  · exact equal
  · exact ((ordinal a).not_mem_self N (eq.symm ▸ order b a after)).elim

theorem numeral_not_clash {a b : Nat} {x : V}
    (h₁ : Internal.Numeral N.mem a x) (h₂ : Internal.Numeral N.mem b x) : a = b :=
  N.numeral_injective (((N.numeral_def _ _).mp h₁).symm.trans ((N.numeral_def _ _).mp h₂))

theorem row_unique {rows count i t a b t' a' b' : V}
    (hf : Internal.FunctionOn N.mem rows count) (hi : N.mem i count)
    (h : Internal.RowAt N.mem rows i t a b) (h' : Internal.RowAt N.mem rows i t' a' b') :
    t = t' ∧ a = a' ∧ b = b' := by
  obtain ⟨p, r, fp, hp, params⟩ := h
  obtain ⟨q, s, fq, hq, params'⟩ := h'
  obtain ⟨_, _, one⟩ := hf.1 i hi
  have same := (one p fp).trans (one q fq).symm
  subst q
  obtain ⟨tagEq, argsEq⟩ := Internal.orderedPair_injective hp hq
  subst s
  exact ⟨tagEq, Internal.orderedPair_injective params params'⟩

noncomputable def PairBound (a b : V) : V := N.power (N.power (N.union₂ a b))

theorem in_pairBound {a b x y : V} (ha : N.mem x a) (hb : N.mem y b) :
    N.mem (N.orderedPair x y) (N.PairBound a b) :=
  N.orderedPair_bound ((N.mem_union₂ _ _ _).mpr (Or.inl ha)) ((N.mem_union₂ _ _ _).mpr (Or.inr hb))

/-- Every assignment is a set of pair codes in a single common
finite powerset bound. -/
theorem assignment_bound {g a b : V} (h : Internal.FunctionInto N.mem g a b) :
    N.Subset g (N.PairBound a b) := by
  intro p hp
  obtain ⟨x, y, hx, code⟩ := h.1.2 p hp
  have eq := (N.orderedPair_iff x y p).mp code
  subst p
  exact N.in_pairBound hx (h.2 x hx y ⟨_, hp, code⟩)

theorem assignment_space (arity stage : V) :
    ∃ space, ∀ env, N.mem env space ↔ Internal.FunctionInto N.mem env arity stage := by
  have described := Definable.functionInto (N := N) (n := 3) (i := 0) (j := 1) (k := 2)
    (by decide) (by decide) (by decide)
  obtain ⟨space, spec⟩ := N.separate [stage] described (N.power (N.PairBound arity stage)) arity
  refine ⟨space, fun env => (spec env).trans ?_⟩
  exact ⟨And.right, fun h => ⟨(N.mem_power _ _).mpr (N.assignment_bound h), h⟩⟩

end PalomarI3380.SquareRepresentation.SetContext
