module
public import I3_334Support.SetTheory.Order.Cardinal
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic

variable {A V : Type} {M : Algebra A}

namespace SetContext

variable (N : SetContext M V)

def AllPowers (graph stage : V) : Prop :=
  ∀ x, N.mem x stage ↔ ∃ i previous, Internal.At N.mem graph i previous ∧ N.Subset x previous

theorem allPowers_exists (graph : V) : ∃ stage, N.AllPowers graph stage := by
  have pred := Definable.powerset (N := N) (n := 2) (i := 0) (j := 1) (by decide) (by decide)
  obtain ⟨allPowers, specifies⟩ := N.image [] pred (fun x y z first next =>
      N.ext y z fun v => (first v).trans (next v).symm) (N.range graph)
  refine ⟨N.union allPowers, fun x => ?_⟩
  rw [N.mem_union]
  constructor
  · rintro ⟨p, hp, hx⟩
    obtain ⟨previous, pri, sets⟩ := (specifies p).mp hp
    obtain ⟨i, atI⟩ := (N.mem_range _ _).mp pri
    exact ⟨i, previous, atI, (sets x).mp hx⟩
  · rintro ⟨i, previous, atI, sub⟩
    exact ⟨N.power previous, (specifies _).mpr ⟨previous, (N.mem_range _ _).mpr ⟨i, atI⟩,
      N.mem_power previous⟩, (N.mem_power _ _).mpr sub⟩

theorem allPowers_unique {graph a b : V} (ha : N.AllPowers graph a) (hb : N.AllPowers graph b) :
    a = b := N.ext a b fun x => (ha x).trans (hb x).symm

end SetContext

namespace Definable

variable {N : SetContext M V} {n i j : Nat}

theorem allPowers (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun s => N.AllPowers (s i) (s j)) := by
  have code := graphValue (N := N) (n := n + 3) (i := i + 3) (j := 1) (k := 0)
    (by omega) (by omega) (by omega)
  have sub := subset (N := N) (n := n + 3) (i := 2) (j := 0) (by omega) (by omega)
  exact all (iff (mem (i := 0) (j := j + 1) (by omega) (by omega)) (ex (ex (code.and sub))))

theorem successor (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun s => Internal.Succ N.mem (s i) (s j)) :=
  all (iff (mem (i := 0) (j := j + 1) (by omega) (by omega))
    ((mem (i := 0) (j := i + 1) (by omega) (by omega)).or
      (eq (i := 0) (j := i + 1) (by omega) (by omega))))

end Definable

namespace SetContext

variable (N : SetContext M V)

theorem internal_succ (a b : V) : Internal.Succ N.mem a b ↔ b = N.succ a :=
  ⟨fun h => N.ext b (N.succ a) fun x => (h x).trans (N.mem_succ a x).symm,
    fun h => h.symm ▸ N.mem_succ a⟩

structure Hierarchy (height graph : V) : Prop where
  functionOn : Internal.FunctionOn N.mem graph (N.succ height)
  members : ∀ b stage, Internal.At N.mem graph b stage →
    ∀ x, N.mem x stage ↔ ∃ a, N.mem a b ∧ ∃ earlier, Internal.At N.mem graph a earlier ∧ N.Subset x earlier

def Rank (height stage : V) : Prop :=
  N.Ordinal height ∧ ∃ graph, N.Hierarchy height graph ∧ Internal.At N.mem graph height stage

private noncomputable def rankRecursion (height : V) (s : N.Ordinal height) : SetRecursion N where
  domain := N.succ height
  orderKey := height
  updateKey := height
  order := fun _ => N.mem
  order_formula := Definable.membership_relation
  wellOrder := (N.ordinal_succ s).ordered
  update := fun _ _ => N.AllPowers
  update_formula := fun _ _ h₁ h₂ => Definable.allPowers h₁ h₂
  update_exists _ := N.allPowers_exists
  update_unique _ _ _ _ := N.allPowers_unique

private theorem rankCut {height : V} (ho : N.Ordinal height) {x bound : V}
    (hx : N.mem x (N.succ height)) (h : (N.rankRecursion height ho).IsCut x bound) : bound = x :=
  N.ext bound x fun z => (h z).trans ⟨And.right, fun hz => ⟨(N.ordinal_succ ho).transitive x hx z hz, hz⟩⟩

private theorem solution_iff_hierarchy {height graph : V} (ho : N.Ordinal height) :
    (N.rankRecursion height ho).Solution (N.succ height) graph ↔ N.Hierarchy height graph := by
  constructor
  · intro h
    refine ⟨h.functionOn, fun b stage out x => ?_⟩
    have hb := SetRecursion.at_domain h.functionOn out
    obtain ⟨bound, prior, output, cut, restr, v, computes⟩ := h.agrees b hb
    have same := N.rankCut ho hb cut
    subst bound
    obtain ⟨w, _, one⟩ := h.functionOn.1 b hb
    have equal := (one output v).trans (one stage out).symm
    subst output
    refine (computes x).trans ?_
    constructor
    · rintro ⟨a, earlier, atPrior, sub⟩
      obtain ⟨inside, before⟩ := (N.restricts_value restr).mp atPrior
      exact ⟨a, inside, earlier, before, sub⟩
    · rintro ⟨a, ha, earlier, before, sub⟩
      exact ⟨a, earlier, (N.restricts_value restr).mpr ⟨ha, before⟩, sub⟩
  · intro h
    refine ⟨h.functionOn, fun b hb => ?_⟩
    obtain ⟨value, out, _⟩ := h.functionOn.1 b hb
    let prior := N.restrictGraph graph b
    have restriction := N.restricts_canonical graph b
    have cut : (N.rankRecursion height ho).IsCut b b := fun x =>
      ⟨fun hx => ⟨(N.ordinal_succ ho).transitive b hb x hx, hx⟩, And.right⟩
    refine ⟨b, prior, value, cut, restriction, out, fun x => (h.members b value out x).trans ?_⟩
    constructor
    · rintro ⟨a, ha, earlier, next, sub⟩
      exact ⟨a, earlier, (N.restricts_value restriction).mpr ⟨ha, next⟩, sub⟩
    · rintro ⟨a, earlier, hValue, sub⟩
      have ⟨ha, atFull⟩ := (N.restricts_value restriction).mp hValue
      exact ⟨a, ha, earlier, atFull, sub⟩

theorem rank_exists {height : V} (ho : N.Ordinal height) : ∃ stage, N.Rank height stage := by
  obtain ⟨f, computed⟩ := (N.rankRecursion height ho).solution_exists
  have h := (N.solution_iff_hierarchy ho).mp computed
  obtain ⟨y, hy, _⟩ := h.functionOn.1 height ((N.mem_succ _ _).mpr (Or.inr rfl))
  exact ⟨y, ho, f, h, hy⟩

theorem hierarchy_unique {height f g : V} (ho : N.Ordinal height)
    (hf : N.Hierarchy height f) (hg : N.Hierarchy height g) : f = g :=
  let recursion := N.rankRecursion height ho
  recursion.solution_unique recursion.initial_domain ((N.solution_iff_hierarchy ho).mpr hf)
    ((N.solution_iff_hierarchy ho).mpr hg)

theorem rank_unique {height a b : V} (ha : N.Rank height a) (hb : N.Rank height b) : a = b := by
  obtain ⟨ho, f, hf, result⟩ := ha
  obtain ⟨_, g, hg, result'⟩ := hb
  cases N.hierarchy_unique ho hf hg
  obtain ⟨_, _, single⟩ := hf.functionOn.1 height ((N.mem_succ _ _).mpr (Or.inr rfl))
  exact (single a result).trans (single b result').symm

end SetContext
end PalomarI3380.SquareRepresentation
