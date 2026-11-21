module
public import I3_380.RecursionExistence
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic

variable {A V : Type} {M : Algebra A} (N : SetContext M V)

theorem order_induction {r : V → V → Prop} {a : V} (ordered : N.WellOrderOn r a)
    (params : List V) {P : (Nat → V) → Prop}
    (definable : N.square.Definable (params.length + 2) P)
    (step : ∀ x, N.mem x a → (∀ y, N.mem y a → r y x → P (parameterEnv params y a)) →
      P (parameterEnv params x a)) :
    ∀ x, N.mem x a → P (parameterEnv params x a) := by
  classical
  obtain ⟨bad, desc⟩ := N.separate params definable.not a a
  have subset : N.Subset bad a := fun x hx => ((desc x).mp hx).1
  intro x hx
  apply Classical.byContradiction
  intro absent
  obtain ⟨x₀, hx₀, minimum⟩ := ordered.least bad subset ⟨x, (desc x).mpr ⟨hx, absent⟩⟩
  apply ((desc x₀).mp hx₀).2
  apply step x₀ (subset x₀ hx₀)
  intro y ay yx
  apply Classical.byContradiction
  intro no
  have wrong := (desc y).mpr ⟨ay, no⟩
  rcases minimum y wrong with same | reverse
  · exact ordered.irrefl x₀ (subset x₀ hx₀) (same.symm ▸ yx)
  · exact WellOrderOn.asymm N ordered ay (subset x₀ hx₀) yx reverse

structure OrderTypeWitness (r : V → V → Prop) (domain height graph : V) : Prop where
  ordinal : N.Ordinal height
  functionOn : Internal.FunctionOn N.mem graph domain
  onto : N.IsRange graph height
  order : ∀ x₁ x₂ y₁ y₂, Internal.At N.mem graph x₁ y₁ → Internal.At N.mem graph x₂ y₂ →
    (r x₁ x₂ ↔ N.mem y₁ y₂)

def OrderType (r : V → V → Prop) (domain height : V) : Prop :=
  ∃ graph, N.OrderTypeWitness r domain height graph

variable {R : V → V → V → Prop}

private def typeRecursion (domain key : V) (definition : Definable.Relation3 N R)
    (ordered : N.WellOrderOn (R key) domain) : SetRecursion N where
  domain := domain
  orderKey := key
  updateKey := key
  order := R
  order_formula := definition
  wellOrder := ordered
  update _ _ graph result := N.IsRange graph result
  update_formula := fun _ _ h₁ h₂ => Definable.range h₁ h₂
  update_exists _ := N.range_exists
  update_unique _ _ _ _ := N.range_unique

private theorem type_recurrence (domain key : V) (definition : Definable.Relation3 N R)
    (ordered : N.WellOrderOn (R key) domain) {f x y : V}
    (sol : (N.typeRecursion domain key definition ordered).Solution domain f) (hx : N.mem x domain)
    (value : Internal.At N.mem f x y) :
    ∀ z, N.mem z y ↔ ∃ a, N.mem a domain ∧ R key a x ∧ Internal.At N.mem f a z := by
  obtain ⟨cut, prior, output, hcut, restr, atValue, computes⟩ := sol.agrees x hx
  obtain ⟨v, _, one⟩ := sol.functionOn.1 x hx
  have same := (one output atValue).trans (one y value).symm
  subst output
  intro z
  refine (computes z).trans ?_
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨before, out⟩ := (N.restricts_value restr).mp ha
    obtain ⟨dom, order⟩ := (hcut a).mp before
    exact ⟨a, dom, order, out⟩
  · rintro ⟨a, ha, before, value⟩
    exact ⟨a, (N.restricts_value restr).mpr ⟨(hcut a).mpr ⟨ha, before⟩, value⟩⟩

/-- Every model-internal set wellorder is isomorphic to a unique ordinal.
The construction uses the range of the graph computed up to each point. -/
theorem orderType_exists (domain key : V) (formula : Definable.Relation3 N R)
    (ordered : N.WellOrderOn (R key) domain) :
    ∃ height, N.OrderType (R key) domain height := by
  let recursion := N.typeRecursion domain key formula ordered
  obtain ⟨f, sol⟩ := recursion.solution_exists
  let height := N.range f
  have fAt (x y : V) (hx : N.mem x domain) (hxy : Internal.At N.mem f x y) :=
    N.type_recurrence domain key formula ordered sol hx hxy
  have allOrd : ∀ x, N.mem x domain → ∀ y, Internal.At N.mem f x y → N.Ordinal y := by
    let defn := Definable.all
      ((Definable.graphValue (N := N) (n := 4) (i := 3) (j := 1) (k := 0) (by decide) (by decide) (by decide)).implies
        (Definable.ordinal (N := N) (n := 4) (i := 0) (by decide)))
    apply N.order_induction ordered [f] defn
    intro x hx received y atXY
    refine N.ordinal_of_transitive_members ?_ ?_
    · intro z hz t ht
      obtain ⟨a, ha, earlier, fz⟩ := (fAt x y hx atXY z).mp hz
      obtain ⟨b, hb, evenEarlier, ft⟩ := (fAt a z ha fz t).mp ht
      exact (fAt x y hx atXY t).mpr ⟨b, hb, ordered.trans b a x hb ha hx evenEarlier earlier, ft⟩
    · intro z hz
      obtain ⟨a, ha, earlier, fz⟩ := (fAt x y hx atXY z).mp hz
      exact received a ha earlier z fz
  have order {x z y w : V} (hx : N.mem x domain) (hz : N.mem z domain)
      (fXY : Internal.At N.mem f x y) (fZW : Internal.At N.mem f z w)
      (ordered : R key x z) : N.mem y w :=
    (fAt z w hz fZW y).mpr ⟨x, hx, ordered, fXY⟩
  have one {x z y : V} (hx : N.mem x domain) (hz : N.mem z domain)
      (fXY : Internal.At N.mem f x y) (fZY : Internal.At N.mem f z y) : x = z := by
    rcases ordered.compare x z hx hz with first | same | second
    · exact ((allOrd x hx y fXY).not_mem_self N (order hx hz fXY fZY first)).elim
    · exact same
    · exact ((allOrd x hx y fXY).not_mem_self N (order hz hx fZY fXY second)).elim
  have inHeight (y : V) (hy : N.mem y height) : N.Ordinal y := by
    obtain ⟨x, h⟩ := (N.mem_range f y).mp hy
    exact allOrd x (SetRecursion.at_domain sol.functionOn h) y h
  have ht : N.Transitive height := by
    intro y hy z hz
    obtain ⟨x, atXY⟩ := (N.mem_range f y).mp hy
    obtain ⟨u, hu, pred, fUZ⟩ := (fAt x y (SetRecursion.at_domain sol.functionOn atXY) atXY z).mp hz
    exact (N.mem_range f z).mpr ⟨u, fUZ⟩
  refine ⟨height, f, ⟨N.ordinal_of_transitive_members ht inHeight, sol.functionOn, N.mem_range f, ?_⟩⟩
  intro x₂ z y w hfy hfw
  have hx := SetRecursion.at_domain sol.functionOn hfy
  have hz := SetRecursion.at_domain sol.functionOn hfw
  refine ⟨order hx hz hfy hfw, fun rel => ?_⟩
  obtain ⟨u, hu, earlier, found⟩ := (fAt z w hz hfw y).mp rel
  exact one hu hx found hfy ▸ earlier

theorem orderType_unique (domain key : V) (definition : Definable.Relation3 N R)
    (ordered : N.WellOrderOn (R key) domain) {a b : V}
    (ha : N.OrderType (R key) domain a) (hb : N.OrderType (R key) domain b) :
    a = b := by
  let recursion := N.typeRecursion domain key definition ordered
  have reconstruct (height graph : V) (h : N.OrderTypeWitness (R key) domain height graph) :
      recursion.Solution domain graph := by
    refine ⟨h.functionOn, fun x hx => ?_⟩
    obtain ⟨cut, hCut⟩ := recursion.cut_exists x
    let prior := N.restrictGraph graph cut
    have hPrior := N.restricts_canonical graph cut
    obtain ⟨y, hY, _⟩ := h.functionOn.1 x hx
    refine ⟨cut, prior, y, hCut, hPrior, hY, fun z => ?_⟩
    have yIn : N.mem y height := (h.onto y).mpr ⟨x, hY⟩
    constructor
    · intro zy
      obtain ⟨t, tGraph⟩ := (h.onto z).mp (h.ordinal.transitive y yIn z zy)
      exact ⟨t, (N.restricts_value hPrior).mpr ⟨(hCut t).mpr
        ⟨SetRecursion.at_domain h.functionOn tGraph, (h.order _ _ _ _ tGraph hY).mpr zy⟩, tGraph⟩⟩
    · rintro ⟨t, ht⟩
      have ⟨inside, value⟩ := (N.restricts_value hPrior).mp ht
      exact (h.order _ _ _ _ value hY).mp ((hCut t).mp inside).2
  obtain ⟨f, hf⟩ := ha
  obtain ⟨g, hg⟩ := hb
  have eq := recursion.solution_unique recursion.initial_domain (reconstruct a f hf) (reconstruct b g hg)
  subst g
  exact N.range_unique hf.onto hg.onto

end PalomarI3380.SquareRepresentation.SetContext
