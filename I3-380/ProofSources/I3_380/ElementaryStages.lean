module
public import I3_380.BoundedSatisfaction
public import I3_380.CriticalPoint
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic SetContext

variable {A V : Type} {M : Algebra A}

namespace Definable

variable {N : NamedModel M V}

theorem elementaryIncluded {n w a b : Nat} (hw : w < n) (ha : a < n) (hb : b < n) :
    N.square.Definable n (fun s => Internal.ElementaryIncluded N.mem (s w) (s a) (s b)) := by
  let body := SetFormula.elementaryIncluded 2 1 0
  have scope : SetFormula.Scoped 3 (SetFormula.elementaryIncluded 2 1 0) :=
    (checkBound_sound _ _).mp (by decide +kernel)
  have domain : N.square.Definable 3 (fun s => Internal.ElementaryIncluded N.mem (s 0) (s 1) (s 2)) :=
    of_levels (S := N.square) (body := body) scope
      (p := fun s => Internal.ElementaryIncluded N.mem (s 2) (s 1) (s 0))
      (fun _ _ => SetFormula.holds_elementaryIncluded (by decide) (by decide) (by decide))
  let mapping (i : Nat) := if i = 0 then w else if i = 1 then a else b
  have lengths : ∀ i, i < 3 → mapping i < n := by
    intro i _
    unfold mapping
    split
    · exact hw
    · split
      · exact ha
      · exact hb
  exact domain.reindex mapping lengths

end Definable

namespace NamedModel

variable (N : NamedModel M V)

theorem functionInto_mono {f d a b : V} (h : Internal.FunctionInto N.mem f d a)
    (sub : N.Subset a b) : Internal.FunctionInto N.mem f d b :=
  ⟨h.1, fun x hx y hy => sub y (h.2 x hx y hy)⟩

theorem elementary_refl (w stage : V) : Internal.ElementaryIncluded N.mem w stage stage :=
  ⟨N.subset_refl _, fun _ _ _ _ _ _ _ _ => Iff.rfl⟩

theorem elementary_trans {w a b c : V} (h : Internal.ElementaryIncluded N.mem w a b)
    (k : Internal.ElementaryIncluded N.mem w b c) :
    Internal.ElementaryIncluded N.mem w a c :=
  ⟨N.subset_trans h.1 k.1, fun p q r code i hi env typed =>
    (h.2 p q r code i hi env typed).trans
      (k.2 p q r code i hi env (N.functionInto_mono typed h.1))⟩

theorem absolute_elementaryIncluded (w a b : N.Active) (omega : Internal.Omega N.mem w.val) :
    Internal.ElementaryIncluded N.localMem w a b ↔ Internal.ElementaryIncluded N.mem w.val a.val b.val := by
  constructor
  · intro h
    have sub := (N.absolute_subset a b).mp h.1
    refine ⟨sub, fun arity count rows code i hi env typed => ?_⟩
    let ar : N.Active := ⟨arity, active_transitive N.laws w.property code.1⟩
    let co : N.Active := ⟨count, active_transitive N.laws w.property code.2.1⟩
    let ro : N.Active := ⟨rows, N.syntax_active omega w.property code⟩
    let ix : N.Active := ⟨i, active_transitive N.laws co.property hi⟩
    let e : N.Active := ⟨env, N.assignment_active typed ar.property a.property⟩
    have truth := h.2 ar co ro ((N.absolute_code w ar co ro).mpr code) ix hi e
      ((N.absolute_functionInto e ar a).mpr typed)
    exact (N.absolute_satisfiesAt omega w.property ar co ro a ix e code hi typed).symm.trans
      (truth.trans (N.absolute_satisfiesAt omega w.property ar co ro b ix e code hi
        (N.functionInto_mono typed sub)))
  · intro h
    refine ⟨(N.absolute_subset a b).mpr h.1, fun arity count rows code i hi env typed => ?_⟩
    have ambient := (N.absolute_code w arity count rows).mp code
    have e := (N.absolute_functionInto env arity a).mp typed
    exact (N.absolute_satisfiesAt omega w.property arity count rows a i env ambient hi e).trans
      ((h.2 _ _ _ ambient _ hi _ e).trans
        (N.absolute_satisfiesAt omega w.property arity count rows b i env ambient hi
          (N.functionInto_mono e h.1)).symm)

theorem preserves_elementaryIncluded (w a b : N.Active) (omega : Internal.Omega N.mem w.val) :
    Internal.ElementaryIncluded N.mem w.val a.val b.val ↔
      Internal.ElementaryIncluded N.mem w.val (N.embedding a).val (N.embedding b).val := by
  let p := SetFormula.elementaryIncluded 0 1 2
  let env := N.threeValues w a b
  have scope : SetFormula.Scoped 3 (SetFormula.elementaryIncluded 0 1 2) :=
    (checkBound_sound _ _).mp (by decide +kernel)
  have before := SetFormula.holds_elementaryIncluded (E := N.localMem) (d := 3)
    (env := env) (default := w) (w := 0) (a := 1) (b := 2) (by decide) (by decide) (by decide)
  have after := SetFormula.holds_elementaryIncluded (E := N.localMem) (d := 3)
    (env := N.embedding ∘ env) (default := N.embedding w) (w := 0) (a := 1) (b := 2)
    (by decide) (by decide) (by decide)
  change SetFormula.holds N.localMem p 3 (N.embedding ∘ env) (N.embedding w) ↔
    Internal.ElementaryIncluded N.localMem (N.embedding w) (N.embedding a) (N.embedding b) at after
  have preserved := N.preserves_builder p 3 scope env w
  have wFixed := N.fixes_omega w omega
  rw [wFixed] at after preserved
  exact (N.absolute_elementaryIncluded w a b omega).symm.trans
    (before.symm.trans (preserved.trans (after.trans (N.absolute_elementaryIncluded w _ _ omega))))

theorem critical_elementary {w : V} (omega : Internal.Omega N.mem w) (hW : N.square.activePoint w)
    {point small : N.Active} (crit : N.Critical point small) :
    Internal.ElementaryIncluded N.mem w small.val (N.embedding small).val := by
  have later := (N.preserves_rank point small).mp crit.rank
  refine ⟨N.rank_subset crit.rank later (later.1.transitive point.val crit.movesUp),
    fun arity count rows code i hi env typed => ?_⟩
  let a : N.Active := ⟨arity, active_transitive N.laws hW code.1⟩
  let c : N.Active := ⟨count, active_transitive N.laws hW code.2.1⟩
  let r : N.Active := ⟨rows, N.syntax_active omega hW code⟩
  let ix : N.Active := ⟨i, active_transitive N.laws c.property hi⟩
  let assignment : N.Active := ⟨env, N.assignment_active typed a.property small.property⟩
  have equal : N.embedding assignment = assignment := by
    apply N.fixes_function assignment a typed.1 (N.fixes_natural omega hW a code.1)
    intro x y edge
    have hx := SetRecursion.at_domain typed.1 edge
    have xIn := (N.omega_ordinal omega).transitive arity code.1 x.val hx
    exact ⟨N.fixes_natural omega hW x xIn, crit.fixedBelow y (typed.2 x.val hx y.val edge)⟩
  have result := N.preserves_satisfiesAt omega hW a c r small ix assignment code hi typed
  rw [equal] at result
  exact result

end NamedModel
end PalomarI3380.SquareRepresentation
