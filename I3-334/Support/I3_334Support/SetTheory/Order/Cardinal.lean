module
public import I3_334Support.SetTheory.Order.WellOrdering
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic

variable {A V : Type} {M : Algebra A}

namespace Definable

variable {N : SetContext M V} {n i j : Nat}

theorem injects (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun s => N.Injects (s i) (s j)) := by
  have funInto := functionInto (N := N) (n := n + 1) (i := 0) (j := i + 1) (k := j + 1)
    (by omega) (by omega) (by omega)
  have atX := graphValue (N := N) (n := n + 4) (i := 3) (j := 2) (k := 0)
    (by omega) (by omega) (by omega)
  have atY := graphValue (N := N) (n := n + 4) (i := 3) (j := 1) (k := 0)
    (by omega) (by omega) (by omega)
  have eq := Definable.eq (S := N.square) (n := n + 4) (i := 2) (j := 1) (by omega) (by omega)
  have hInj := all (all (all (atX.implies (atY.implies eq))))
  refine (ex (funInto.and hInj)).congr fun s => ?_
  exact ⟨fun ⟨f, ⟨hf, into⟩, one⟩ => ⟨f, hf, fun x y h =>
      into x (SetRecursion.at_domain hf h) y h, one⟩,
    fun ⟨f, h⟩ => ⟨f, ⟨h.functionOn, fun x hx y atF => h.into x y atF⟩, h.unique⟩⟩

end Definable

namespace SetContext

variable (N : SetContext M V)

theorem injects_sub {a b : V} (h : N.Subset a b) : N.Injects a b := by
  obtain ⟨f, onFunction, values⟩ := N.functionOf [] (Definable.eq (S := N.square)
    (n := 2) (i := 0) (j := 1) (by decide) (by decide)) (fun _ _ _ hy hz => hy.symm.trans hz)
    a (fun x _ => ⟨x, rfl⟩)
  refine ⟨f, onFunction, ?_, ?_⟩
  · intro x y hx
    have ⟨inA, same⟩ := (values x y).mp hx
    have eq : x = y := same
    exact eq ▸ h x inA
  · intro x y z hx hy
    exact ((values x z).mp hx).2.trans (((values y z).mp hy).2).symm

theorem injects_trans {a b c : V} (ab : N.Injects a b) (bc : N.Injects b c) : N.Injects a c := by
  obtain ⟨f, hf⟩ := ab
  obtain ⟨g, hg⟩ := bc
  have definable := Definable.ex (
    (Definable.graphValue (N := N) (n := 5) (i := 3) (j := 1) (k := 0)
      (by decide) (by decide) (by decide)).and
    (Definable.graphValue (N := N) (n := 5) (i := 4) (j := 0) (k := 2)
      (by decide) (by decide) (by decide)))
  let property := fun x z => ∃ y, Internal.At N.mem f x y ∧ Internal.At N.mem g y z
  have determinate (x y z : V) (hx : property x y) (hy : property x z) : y = z := by
    obtain ⟨i, fi, gi⟩ := hx
    obtain ⟨j, fj, gj⟩ := hy
    obtain ⟨k, _, only⟩ := hf.functionOn.1 x (SetRecursion.at_domain hf.functionOn fi)
    have same := (only i fi).trans (only j fj).symm
    subst j
    obtain ⟨w, _, alone⟩ := hg.functionOn.1 i (hf.into x i fi)
    exact (alone y gi).trans (alone z gj).symm
  have total (x : V) (hx : N.mem x a) : ∃ z, property x z := by
    obtain ⟨y, fy, _⟩ := hf.functionOn.1 x hx
    obtain ⟨z, gz, _⟩ := hg.functionOn.1 y (hf.into x y fy)
    exact ⟨z, y, fy, gz⟩
  obtain ⟨composition, func, values⟩ := N.functionOf [f,g] definable determinate a total
  refine ⟨composition, func, ?_, ?_⟩
  · intro x y hx
    obtain ⟨_, z, _, gz⟩ := (values x y).mp hx
    exact hg.into z y gz
  · intro x y z hx hy
    obtain ⟨_, i, ix, iz⟩ := (values x z).mp hx
    obtain ⟨_, j, jy, jz⟩ := (values y z).mp hy
    have same := hg.unique i j z iz jz
    cases same
    exact hf.unique x y i ix jy

def Equinumerous (a b : V) : Prop := N.Injects a b ∧ N.Injects b a

theorem orderType_cardinal {a height : V} {r : V → V → Prop} (wellOrder : N.WellOrderOn r a)
    (type : N.OrderType r a height) : N.Equinumerous a height := by
  obtain ⟨f, hf⟩ := type
  have into (x y : V) (h : Internal.At N.mem f x y) : N.mem y height := (hf.onto y).mpr ⟨x, h⟩
  have injection (x y z : V) (hx : Internal.At N.mem f x z) (hy : Internal.At N.mem f y z) : x = y := by
    have no := (hf.ordinal.of_mem N (into x z hx)).not_mem_self N
    rcases wellOrder.compare x y (SetRecursion.at_domain hf.functionOn hx)
      (SetRecursion.at_domain hf.functionOn hy) with left | same | right
    · exact (no ((hf.order _ _ _ _ hx hy).mp left)).elim
    · exact same
    · exact (no ((hf.order _ _ _ _ hy hx).mp right)).elim
  obtain ⟨inverse, graph, values⟩ := N.functionOf [f] (Definable.graphValue (N := N)
    (n := 3) (i := 2) (j := 1) (k := 0) (by decide) (by decide) (by decide))
    (fun x y z hy hz => injection y z x hy hz) height (fun x hx => (hf.onto x).mp hx)
  refine ⟨⟨f, hf.functionOn, into, injection⟩, ⟨inverse, graph, ?_, ?_⟩⟩
  · intro x y atInverse
    exact SetRecursion.at_domain hf.functionOn ((values x y).mp atInverse).2
  · intro x y z hx hy
    have vx := ((values x z).mp hx).2
    have vy := ((values y z).mp hy).2
    obtain ⟨w, _, one⟩ := hf.functionOn.1 z (SetRecursion.at_domain hf.functionOn vx)
    exact (one x vx).trans (one y vy).symm

/-- Least ordinal admitting injections in both directions. Only the two
directions of comparison are needed, so no bijection choice is stored. -/
structure Cardinal (a height : V) : Prop where
  ordinal : N.Ordinal height
  equinumerous : N.Equinumerous a height
  minimal : ∀ x, N.mem x height → ¬N.Equinumerous a x

end SetContext

namespace Definable

variable {N : SetContext M V} {n i j : Nat}

theorem equinumerous (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun s => N.Equinumerous (s i) (s j)) :=
  (injects hi hj).and (injects hj hi)

theorem cardinal (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun s => N.Cardinal (s i) (s j)) := by
  have least := boundedAll hj _ (not (equinumerous (N := N) (n := n + 1) (i := i + 1) (j := 0)
    (by omega) (by omega)))
  refine ((ordinal hj).and ((equinumerous hi hj).and least)).congr fun s => ?_
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun h => ⟨h.ordinal, h.equinumerous, h.minimal⟩⟩

end Definable

namespace SetContext

variable (N : SetContext M V)

theorem cardinal_exists (a : V) : ∃ height, N.Cardinal a height := by
  obtain ⟨relation, ordered⟩ := N.wellOrdering a
  obtain ⟨height, ht⟩ := N.orderType_exists a relation (Definable.graph_relation (N := N)) ordered
  have ordinal : N.Ordinal height := by obtain ⟨_, h⟩ := ht; exact h.ordinal
  have equivalence := N.orderType_cardinal ordered ht
  let bound := N.succ height
  have hBound := N.ordinal_succ ordinal
  obtain ⟨candidates, known⟩ := N.separate [] (Definable.equinumerous (N := N)
    (n := 2) (i := 1) (j := 0) (by decide) (by decide)) bound a
  have existsCandidate : N.NonemptySet candidates :=
    ⟨height, (known height).mpr ⟨(N.mem_succ _ _).mpr (Or.inr rfl), equivalence⟩⟩
  have sub : N.Subset candidates bound := fun x hx => ((known x).mp hx).1
  obtain ⟨least, hl, minimal⟩ := hBound.ordered.least candidates sub existsCandidate
  obtain ⟨hb, eq⟩ := (known least).mp hl
  refine ⟨least, hBound.of_mem N hb, eq, fun x hx h => ?_⟩
  have below : N.mem x bound := hBound.transitive least hb x hx
  have option := (known x).mpr ⟨below, h⟩
  rcases minimal x option with same | reverse
  · exact hBound.ordered.irrefl least hb (same.symm ▸ hx)
  · exact WellOrderOn.asymm N hBound.ordered below hb hx reverse

theorem cardinal_unique {a x y : V} (hx : N.Cardinal a x) (hy : N.Cardinal a y) : x = y := by
  rcases N.ordinal_compare hx.ordinal hy.ordinal with less | eq | greater
  · exact (hy.minimal x less hx.equinumerous).elim
  · exact eq
  · exact (hx.minimal y greater hy.equinumerous).elim


end SetContext
end PalomarI3380.SquareRepresentation
