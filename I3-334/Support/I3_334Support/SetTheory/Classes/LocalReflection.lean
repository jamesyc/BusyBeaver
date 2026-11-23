module
public import I3_334Support.Equations.RecoveredFoundation
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)

abbrev Active := N.square.Domain

def localMem (x y : N.Active) : Prop := N.mem x.val y.val

noncomputable def embedding : N.Active → N.Active := jMap N.laws N.active_closure

theorem embedding_edge (x : N.Active) :
    N.square.rel (M.constant .J) x.val (N.embedding x).val :=
  jMap_edge N.laws N.active_closure x

theorem fixed_iff_self_edge (x : N.Active) :
    N.embedding x = x ↔ N.square.rel (M.constant .J) x.val x.val := by
  constructor
  · intro h
    have edge := N.embedding_edge x
    rwa [h] at edge
  · intro h
    exact Subtype.ext (j_single_valued N.laws N.active_closure (N.embedding_edge x) h)

theorem preserves_builder (p : SetFormula) (n : Nat) (h : SetFormula.Scoped n p)
    (env : Nat → N.Active) (default : N.Active) :
    SetFormula.holds N.localMem p n env default ↔
      SetFormula.holds N.localMem p n (N.embedding ∘ env) (N.embedding default) := by
  have commute : SetFormula.assignment n (N.embedding ∘ env) (N.embedding default) =
      N.embedding ∘ SetFormula.assignment n env default := by
    funext i
    by_cases hi : i < n <;> simp [SetFormula.assignment, hi]
  unfold SetFormula.holds
  rw [commute]
  exact local_elementarity N.laws N.active_closure (p n) n h _

theorem preserves_membership (x y : N.Active) :
    N.localMem x y ↔ N.localMem (N.embedding x) (N.embedding y) := by
  let member := LocalRelation.member N.laws N.active_closure
  have eq := LocalRelation.reflects N.laws N.active_closure member (N.embedding_edge x) (N.embedding_edge y)
  exact ⟨fun h => (eq.mp ⟨h, y.property⟩).1,
    fun h => (eq.mpr ⟨h, (N.embedding y).property⟩).1⟩

theorem absolute_subset (a b : N.Active) :
    (∀ x, N.localMem x a → N.localMem x b) ↔ N.Subset a.val b.val := by
  constructor
  · intro h x hx
    exact h ⟨x, active_transitive N.laws a.property hx⟩ hx
  · exact fun h x hx => h x.val hx

theorem absolute_empty (a : N.Active) :
    Internal.Empty N.localMem a ↔ Internal.Empty N.mem a.val := by
  constructor
  · intro h x hx
    exact h ⟨x, active_transitive N.laws a.property hx⟩ hx
  · exact fun h x hx => h x.val hx

theorem fixes_empty (a : N.Active) (h : Internal.Empty N.mem a.val) : N.embedding a = a := by
  let env := fun _ : Nat => a
  have semantic (s : N.Active) :
      SetFormula.holds N.localMem (SetFormula.empty 0) 1 (fun _ => s) s ↔
        Internal.Empty N.mem s.val :=
    (SetFormula.holds_empty (E := N.localMem) (env := fun _ => s) (default := s) (by decide)).trans
      (N.absolute_empty s)
  have preserves := N.preserves_builder (SetFormula.empty 0) 1 (SetFormula.scope_empty (by decide)) env a
  have e : Internal.Empty N.mem (N.embedding a).val :=
    (semantic (N.embedding a)).mp (preserves.mp ((semantic a).mpr h))
  exact Subtype.ext (((N.empty_unique _).mp e).trans ((N.empty_unique _).mp h).symm)

def twoValues (a b : N.Active) : Nat → N.Active :=
  fun i => if i = 0 then a else b

theorem map_twoValues (a b : N.Active) :
    N.embedding ∘ N.twoValues a b = N.twoValues (N.embedding a) (N.embedding b) := by
  funext i
  by_cases h : i = 0 <;> simp [twoValues, h]

theorem preserves_subset (a b : N.Active) :
    N.Subset a.val b.val ↔ N.Subset (N.embedding a).val (N.embedding b).val := by
  let p := SetFormula.subset 0 1
  have sem (x y : N.Active) :
      SetFormula.holds N.localMem p 2 (N.twoValues x y) x ↔ N.Subset x.val y.val := by
    have h := (SetFormula.holds_subset (E := N.localMem) (env := N.twoValues x y) (default := x)
      (a := 0) (b := 1) (d := 2) (by decide) (by decide))
    refine Iff.trans ?_ (N.absolute_subset x y)
    simpa [p, twoValues] using h
  have h := N.preserves_builder p 2 (SetFormula.scope_subset (by decide) (by decide)) (N.twoValues a b) a
  rw [N.map_twoValues] at h
  exact (sem a b).symm.trans (h.trans (sem _ _))

def powerFormula (a b : Nat) : SetFormula :=
  SetFormula.every fun z => SetFormula.iff (SetFormula.mem z b) (SetFormula.subset z a)

theorem powerFormula_scope {d a b : Nat} (ha : a < d) (hb : b < d) :
    SetFormula.Scoped d (powerFormula a b) := by
  simp (disch := omega) only [powerFormula, SetFormula.scope_every, SetFormula.scope_iff,
    SetFormula.scope_mem, SetFormula.scope_subset, and_self]

theorem powerFormula_holds {W : Type} {E : W → W → Prop} {n a b : Nat} {env : Nat → W} {default : W}
    (ha : a < n) (hb : b < n) :
    SetFormula.holds E (powerFormula a b) n env default ↔
      ∀ z, E z (env b) ↔ ∀ w, E w z → E w (env a) := by
  simp (disch := omega) only [powerFormula, SetFormula.holds_every, SetFormula.holds_iff,
    SetFormula.holds_mem, SetFormula.holds_subset, SetFormula.assign_earlier, SetFormula.assign_here]

theorem absolute_power (a b : N.Active) :
    (∀ z, N.localMem z b ↔ ∀ w, N.localMem w z → N.localMem w a) ↔ b.val = N.power a.val := by
  constructor
  · intro h
    apply N.ext
    intro z
    rw [N.mem_power]
    constructor
    · intro hz
      let q : N.Active := ⟨z, active_transitive N.laws b.property hz⟩
      exact (N.absolute_subset q a).mp ((h q).mp hz)
    · intro hz
      let q : N.Active := ⟨z, active_subset N.laws a.property hz⟩
      exact (h q).mpr ((N.absolute_subset q a).mpr hz)
  · rintro h z
    exact (Iff.of_eq (congrArg (N.mem z.val) h)).trans
      ((N.mem_power _ _).trans (N.absolute_subset z a).symm)

theorem preserves_power (a b : N.Active) :
    b.val = N.power a.val ↔ (N.embedding b).val = N.power (N.embedding a).val := by
  have sem (x y : N.Active) :
      SetFormula.holds N.localMem (powerFormula 0 1) 2 (N.twoValues x y) x ↔ y.val = N.power x.val := by
    have h := powerFormula_holds (E := N.localMem) (env := N.twoValues x y) (default := x)
      (a := 0) (b := 1) (n := 2) (by decide) (by decide)
    refine Iff.trans ?_ (N.absolute_power x y)
    simpa [twoValues] using h
  have h := N.preserves_builder (powerFormula 0 1) 2 (powerFormula_scope (by decide) (by decide))
    (N.twoValues a b) a
  rw [N.map_twoValues] at h
  exact (sem a b).symm.trans (h.trans (sem _ _))

theorem fixes_subsets (v : N.Active) (fixed : N.embedding v = v)
    (pointwise : ∀ z : N.Active, N.localMem z v → N.embedding z = z)
    (x : N.Active) (hx : N.Subset x.val v.val) : N.embedding x = x := by
  have inside := (N.preserves_subset x v).mp hx
  rw [fixed] at inside
  apply Subtype.ext
  apply N.ext
  intro z
  constructor
  · intro hz
    let point : N.Active := ⟨z, active_transitive N.laws v.property (inside z hz)⟩
    have same := pointwise point (inside z hz)
    apply (N.preserves_membership point x).mpr
    rw [same]
    exact hz
  · intro hz
    let point : N.Active := ⟨z, active_transitive N.laws v.property (hx z hz)⟩
    have same := pointwise point (hx z hz)
    have member := (N.preserves_membership point x).mp hz
    rwa [same] at member

end PalomarI3380.SquareRepresentation.NamedModel
