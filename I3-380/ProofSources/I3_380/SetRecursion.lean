module
public import I3_380.GraphRange
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic

variable {A V : Type} {M : Algebra A} {N : SetContext M V}

namespace Definable

def Relation4 (N : SetContext M V) (R : V → V → V → V → Prop) : Prop :=
  ∀ {n i j k l : Nat}, i < n → j < n → k < n → l < n →
    N.square.Definable n (fun env => R (env i) (env j) (env k) (env l))

end Definable

/-- Set-length recursion uses a relation whose order and update rules
are fixed formulas in the expanded set model. -/
structure SetRecursion (N : SetContext M V) where
  domain : V
  orderKey : V
  updateKey : V
  order : V → V → V → Prop
  order_formula : Definable.Relation3 N order
  wellOrder : N.WellOrderOn (order orderKey) domain
  update : V → V → V → V → Prop
  update_formula : Definable.Relation4 N update
  update_exists : ∀ x graph, ∃ y, update updateKey x graph y
  update_unique : ∀ x graph y z, update updateKey x graph y → update updateKey x graph z → y = z

namespace SetRecursion

variable (R : SetRecursion N)

abbrev before (x y : V) := R.order R.orderKey x y

def IsCut (x bound : V) : Prop :=
  ∀ y, N.mem y bound ↔ N.mem y R.domain ∧ R.before y x

def IsThrough (x bound : V) : Prop :=
  ∀ y, N.mem y bound ↔ N.mem y R.domain ∧ (R.before y x ∨ y = x)

def Initial (bound : V) : Prop :=
  N.Subset bound R.domain ∧
    ∀ y, N.mem y bound → ∀ x, N.mem x R.domain → R.before x y → N.mem x bound

theorem cut_definable {n i j k l : Nat} (hi : i < n) (hj : j < n) (hk : k < n) (hl : l < n) :
    N.square.Definable n (fun env => ∀ y, N.mem y (env l) ↔
      N.mem y (env i) ∧ R.order (env j) y (env k)) :=
  Definable.all (Definable.iff (Definable.mem (i := 0) (j := l + 1) (by omega) (by omega))
    ((Definable.mem (i := 0) (j := i + 1) (by omega) (by omega)).and
      (R.order_formula (i := j + 1) (j := 0) (k := k + 1) (by omega) (by omega) (by omega))))

theorem through_definable {n i j k l : Nat} (hi : i < n) (hj : j < n) (hk : k < n) (hl : l < n) :
    N.square.Definable n (fun env => ∀ y, N.mem y (env l) ↔
      N.mem y (env i) ∧ (R.order (env j) y (env k) ∨ y = env k)) :=
  Definable.all (Definable.iff (Definable.mem (i := 0) (j := l + 1) (by omega) (by omega))
    ((Definable.mem (i := 0) (j := i + 1) (by omega) (by omega)).and
      ((R.order_formula (i := j + 1) (j := 0) (k := k + 1) (by omega) (by omega) (by omega)).or
        (Definable.eq (i := 0) (j := k + 1) (by omega) (by omega)))))

theorem cut_exists (x : V) : ∃ a, R.IsCut x a :=
  N.separate [x] (R.order_formula (n := 3) (i := 1) (j := 0) (k := 2)
    (by decide) (by decide) (by decide)) R.domain R.orderKey

theorem through_exists (x : V) : ∃ a, R.IsThrough x a :=
  N.separate [x] ((R.order_formula (n := 3) (i := 1) (j := 0) (k := 2)
    (by decide) (by decide) (by decide)).or
      (Definable.eq (n := 3) (i := 0) (j := 2) (by decide) (by decide))) R.domain R.orderKey

theorem cut_initial {x a : V} (hx : N.mem x R.domain) (ha : R.IsCut x a) : R.Initial a := by
  refine ⟨fun y hy => ((ha y).mp hy).1, fun y hy z hz pred => ?_⟩
  have ord := (ha y).mp hy
  exact (ha z).mpr ⟨hz, R.wellOrder.trans z y x hz ord.1 hx pred ord.2⟩

theorem through_initial {x a : V} (hx : N.mem x R.domain) (ha : R.IsThrough x a) : R.Initial a := by
  refine ⟨fun y hy => ((ha y).mp hy).1, fun y hy z hz pred => ?_⟩
  obtain ⟨yd, hxy⟩ := (ha y).mp hy
  exact (ha z).mpr ⟨hz, Or.inl (hxy.elim (fun yx => R.wellOrder.trans z y x hz yd hx pred yx)
    (fun eq => eq ▸ pred))⟩

theorem cut_eq {x a b : V} (ha : R.IsCut x a) (hb : R.IsCut x b) : a = b :=
  N.ext a b fun y => (ha y).trans (hb y).symm

theorem through_eq {x a b : V} (ha : R.IsThrough x a) (hb : R.IsThrough x b) : a = b :=
  N.ext a b fun y => (ha y).trans (hb y).symm

theorem cut_in_initial {x a b : V} (hx : N.mem x a) (init : R.Initial a) (cut : R.IsCut x b) :
    N.Subset b a :=
  fun y hy => let ⟨dy, ordered⟩ := (cut y).mp hy; init.2 x hx y dy ordered

theorem through_in_initial {x a b : V} (hx : N.mem x a) (init : R.Initial a) (cut : R.IsThrough x b) :
    N.Subset b a := fun y hy =>
      let ⟨dy, where_⟩ := (cut y).mp hy
      where_.elim (init.2 x hx y dy) (fun same => same.symm ▸ hx)

theorem initial_domain : R.Initial R.domain :=
  ⟨N.subset_refl _, fun _ _ _ h _ => h⟩

theorem initial_inter {a b : V} (ha : R.Initial a) (hb : R.Initial b) : R.Initial (N.inter a b) := by
  refine ⟨fun x hx => ha.1 x ((N.mem_inter _ _ _).mp hx).1, fun x hx y hy h => ?_⟩
  obtain ⟨xa, xb⟩ := (N.mem_inter a b x).mp hx
  exact (N.mem_inter _ _ _).mpr ⟨ha.2 x xa y hy h, hb.2 x xb y hy h⟩

/-- A solution is an actual graph whose value at each argument is
determined using its own restriction to all predecessors of that argument. -/
structure Solution (R : SetRecursion N) (segment graph : V) : Prop where
  functionOn : Internal.FunctionOn N.mem graph segment
  agrees : ∀ x, N.mem x segment → ∃ cut prior value,
    R.IsCut x cut ∧ N.Restricts graph cut prior ∧ Internal.At N.mem graph x value ∧
      R.update R.updateKey x prior value

def FullSolution (x graph : V) : Prop :=
  ∃ segment, R.IsThrough x segment ∧ R.Solution segment graph

theorem solution_restrict {a b f g : V} (h : R.Solution a f)
    (sub : N.Subset b a) (init : R.Initial b) (restriction : N.Restricts f b g) :
    R.Solution b g := by
  refine ⟨N.restricts_function h.functionOn sub restriction, fun x hx => ?_⟩
  obtain ⟨cut, old, value, hcut, hOld, hValue, update⟩ := h.agrees x (sub x hx)
  have cutBelow := R.cut_in_initial hx init hcut
  let prior := N.restrictGraph g cut
  have restr := N.restricts_canonical g cut
  have priorEq : prior = old := N.restricts_unique (N.restricts_nested cutBelow restriction restr) hOld
  exact ⟨cut, prior, value, hcut, restr, (N.restricts_value restriction).mpr ⟨hx, hValue⟩,
    priorEq.symm ▸ update⟩

end SetRecursion
end PalomarI3380.SquareRepresentation
