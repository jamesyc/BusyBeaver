module
public import I3_334Support.SetTheory.Forcing.AmenableOrder
public import I3_334Support.Equations.LocalRelationAlgebra
public import I3_334Support.SetTheory.Rank.StageSelector
public import I3_334Support.Equations.Ground
@[expose] public section

namespace PalomarI3380.Logic.Expanded

open SquareRepresentation

variable {V : Type} {E G : V → V → Prop}

namespace ClassRelation

/-- The parameter environments may be inspected by the defining predicate. -/
noncomputable def ofParameters (params : List V) (default : V)
    {P : (Nat → V) → Prop} (defn : (square E G).Definable (params.length + 2) P) :
    ClassRelation E G := by
  refine ⟨fun x y => P (parameterEnv params x y),?_⟩
  obtain ⟨p,bound,correct⟩ := defn
  obtain ⟨f,hf,evalF⟩ := binary_class p params default bound
  exact ⟨f,hf,fun env => (evalF env).trans (correct (parameterEnv params (env 0) (env 1)))⟩

end ClassRelation

namespace EquationModel

variable (L : ClassAxioms E G) (inhabited : Nonempty V)

local notation "K" => (L.context inhabited)
local notation "R" => ClassRelation E G

noncomputable def stageSelector : R :=
  ClassRelation.ofParameters [] (K).empty
    ((K).stageChoice_def (n := 2) (x := 0) (s := 1) (by decide) (by decide))

noncomputable def stages : R :=
  ClassRelation.ofParameters [] (K).empty
    ((Definable.eq (S := (ClassRelation.square E G)) (n := 2) (i := 0) (j := 1) (by decide) (by decide)).and
      (Definable.ex (Definable.rank (N := (K)) (n := 3) (i := 0) (j := 1) (by decide) (by decide))))

noncomputable def embedding (j : V) : R :=
  ClassRelation.ofParameters [j] (K).empty (Definable.graphValue (N := (K))
    (n := 3) (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide))

noncomputable def select (r : R) : R := by
  classical
  exact if r = .subset then stageSelector L inhabited else
    ⟨Binary.leastRelation G r.holds,Binary.least_def r.definable⟩

theorem select_subset : select L inhabited (.subset : R) = stageSelector L inhabited := by
  classical
  simp [select]

theorem select_sub (r : R) {x y : V} (h : (select L inhabited r).holds x y) : r.holds x y := by
  classical
  unfold select at h
  split at h
  · subst r
    obtain ⟨_,_,sub,_⟩ := h
    exact sub
  · exact h.1

theorem select_function (minimum : ClassMinimum E G) (r : R) {x y z : V}
    (hy : (select L inhabited r).holds x y) (hz : (select L inhabited r).holds x z) : y = z := by
  classical
  unfold select at hy hz
  split at hy <;> rename_i which
  · rw [ite_eq_left which] at hz
    exact (K).stageChoice_unique hy hz
  · rw [ite_eq_right which] at hz
    exact Binary.least_functional minimum hy hz

theorem select_exists (minimum : ClassMinimum E G) {w : V} (omega : Internal.Omega E w)
    (r : R) (x : V) (h : ∃ y, r.holds x y) : ∃ y, (select L inhabited r).holds x y := by
  classical
  unfold select
  split
  · exact (K).stageChoice_exists omega (L.ordinary.foundation (fun _ => (K).empty)) x
  · exact minimum.least _ r.definable x h

theorem stages_are_range : (stageSelector L inhabited).converse.product (stageSelector L inhabited) =
    stages L inhabited := by
  apply ClassRelation.ext
  intro x y
  change (∃ a, (K).StageChoice a x ∧ (K).StageChoice a y) ↔ x = y ∧ ∃ b, (K).Rank b x
  constructor
  · rintro ⟨a,hx,hy⟩
    exact ⟨(K).stageChoice_unique hx hy,(K).stageChoice_range.mp ⟨a,hx⟩⟩
  · rintro ⟨rfl,h⟩
    obtain ⟨a,ha⟩ := (K).stageChoice_range.mpr h
    exact ⟨a,ha,ha⟩

theorem stages_law :
    (stages L inhabited).product ClassRelation.member.converse =
      (((stages L inhabited).product ClassRelation.member.converse).product
        (stages L inhabited)).product ClassRelation.subset.converse := by
  apply ClassRelation.ext
  intro x y
  change (∃ u, (x = u ∧ ∃ a, (K).Rank a x) ∧ E y u) ↔
    ∃ t, (∃ v, (∃ u, (x = u ∧ ∃ a, (K).Rank a x) ∧ E v u) ∧
      (v = t ∧ ∃ b, (K).Rank b v)) ∧ (K).Subset y t
  constructor
  · rintro ⟨_,⟨rfl,a,rank⟩,member⟩
    obtain ⟨b,t,earlier,before,sub⟩ := ((K).mem_rank_iff rank y).mp member
    exact ⟨t,⟨t,⟨x,⟨rfl,a,rank⟩,(K).rank_member before rank earlier⟩,rfl,b,before⟩,sub⟩
  · rintro ⟨t,⟨v,⟨_,⟨rfl,a,rank⟩,member⟩,same,b,before⟩,sub⟩
    subst v
    exact ⟨x,⟨rfl,a,rank⟩,((K).mem_rank_iff rank y).mpr
      ⟨b,t,((K).rank_member_iff before rank).mp member,before,sub⟩⟩

noncomputable def algebra (stage j : V) : Algebra R :=
  { ClassRelation.algebra E G with
    constant := fun
      | .D => .rankDiagonal stage
      | .J => embedding L inhabited j
      | .U => .top
      | .E => .member
      | .I => .one
      | .T => .subset
      | .S => stages L inhabited
    choice := select L inhabited
    localRel := fun r => LocalTree.relation stage (LocalTree.decode (K) r)
    node := fun r s t => LocalTree.encode (K)
      (.node (LocalTree.decode (K) r) (LocalTree.decode (K) s) (LocalTree.decode (K) t))
  }

end EquationModel
end PalomarI3380.Logic.Expanded
