module
public import I3_380.Logic.SetScope
@[expose] public section

namespace PalomarI3380.Logic.Internal

variable {V : Type} (E : V → V → Prop)

def Transitive (a : V) : Prop := ∀ x, E x a → ∀ y, E y x → E y a
def OrdinalLike (a : V) : Prop := Transitive E a ∧ ∀ x, E x a → Transitive E x

def Hierarchy (graph domain : V) : Prop :=
  FunctionOn E graph domain ∧ ∀ b, E b domain → ∀ stage, At E graph b stage →
    ∀ x, E x stage ↔ ∃ a, E a b ∧ ∃ earlier, At E graph a earlier ∧ ∀ z, E z x → E z earlier

def RankLike (height stage : V) : Prop :=
  OrdinalLike E height ∧ ∃ domain graph,
    Succ E height domain ∧ Hierarchy E graph domain ∧ At E graph height stage

end PalomarI3380.Logic.Internal

namespace PalomarI3380.Logic.SetFormula

variable {V : Type} {E : V → V → Prop} {d : Nat} {env : Nat → V} {default : V}

theorem holds_transitive {a : Nat} (bound : a < d) :
    holds E (transitive a) d env default ↔ Internal.Transitive E (env a) := by
  simp (disch := omega) only [transitive, holds_eachIn, holds_subset, assign_here, assign_earlier,
    Internal.Transitive]

theorem holds_ordinal {a : Nat} (bound : a < d) :
    holds E (ordinal a) d env default ↔ Internal.OrdinalLike E (env a) := by
  simp (disch := omega) only [ordinal, holds_both, holds_transitive, holds_eachIn, assign_here,
    Internal.OrdinalLike]

theorem holds_hierarchy {g a : Nat} (hg : g < d) (ha : a < d) :
    holds E (hierarchy g a) d env default ↔ Internal.Hierarchy E (env g) (env a) := by
  simp (disch := omega) only [hierarchy, holds_both, holds_functionOn, holds_eachIn, holds_every,
    holds_implies, holds_graphValue, holds_iff, holds_mem, holds_someIn, holds_someSet, holds_subset,
    assign_earlier, assign_here, Internal.Hierarchy]

theorem holds_rank {a b : Nat} (ha : a < d) (hb : b < d) :
    holds E (rank a b) d env default ↔ Internal.RankLike E (env a) (env b) := by
  simp (disch := omega) only [rank, holds_both, holds_ordinal, holds_someSet, allOf, holds_successor,
    holds_hierarchy, holds_graphValue, assign_earlier, assign_here, holds_neg, holds_falsity,
    not_false_eq_true, and_true, Internal.RankLike]

theorem scope_transitive {d a : Nat} (h : a < d) : Scoped d (transitive a) := by
  simp (disch := omega) only [transitive, scope_eachIn, scope_subset]

theorem scope_ordinal {d a : Nat} (h : a < d) : Scoped d (ordinal a) := by
  simp (disch := omega) only [ordinal, scope_both, scope_transitive, scope_eachIn, and_self]

theorem scope_hierarchy {d a g : Nat} (ha : a < d) (hg : g < d) : Scoped d (hierarchy g a) := by
  simp (disch := omega) only [hierarchy, scope_both, scope_functionOn, scope_eachIn, scope_every,
    scope_impl, scope_graphValue, scope_iff, scope_mem, scope_someIn, scope_someSet, scope_subset, and_self]

theorem scope_rank {d a b : Nat} (ha : a < d) (hb : b < d) : Scoped d (rank a b) := by
  simp (disch := omega) only [rank, scope_both, scope_ordinal, scope_someSet, allOf, scope_successor,
    scope_hierarchy, scope_graphValue, scope_neg, scope_falsity, and_self]

end PalomarI3380.Logic.SetFormula
