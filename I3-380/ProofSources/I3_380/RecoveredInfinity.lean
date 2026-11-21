module
public import I3_380.LocalReflection
public import I3_380.OmegaSets
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic SetContext

variable {A V : Type} {M : Algebra A}

namespace NamedModel

variable (N : NamedModel M V)

theorem limit_is_inductive {a : V} (ho : N.Ordinal a) (notEmpty : a ≠ N.empty)
    (notSuccessor : ¬∃ b, a = N.succ b) : Internal.Inductive N.mem a := by
  have zero : N.mem N.empty a :=
    ((N.ordinal_subset_iff N.ordinal_empty ho).mp (fun x hx => (N.empty_mem x hx).elim)).resolve_right
      (fun h => notEmpty h.symm)
  refine ⟨⟨N.empty, N.empty_mem, zero⟩, fun b hb => ?_⟩
  have hbOrd := ho.of_mem N.toSetContext hb
  have sub : N.Subset (N.succ b) a := by
    intro x hx
    rcases (N.mem_succ _ _).mp hx with h | rfl
    · exact ho.transitive b hb x h
    · exact hb
  have contains : N.mem (N.succ b) a :=
    ((N.ordinal_subset_iff (N.ordinal_succ hbOrd) ho).mp sub).resolve_right
      (fun h => notSuccessor ⟨b, h.symm⟩)
  exact ⟨N.succ b, N.mem_succ b, contains⟩

def RankFixed (a : V) : Prop :=
  ∀ v, N.Rank a v → N.square.activePoint v →
    N.square.rel (M.constant .J) v v ∧ ∀ x, N.mem x v → N.square.rel (M.constant .J) x x

private theorem rank_fixed_definable {n i : Nat} (hi : i < n) :
    N.square.Definable n (fun s => N.RankFixed (s i)) := by
  have hRank := Definable.rank (N := N.toSetContext) (n := n + 1) (i := i + 1) (j := 0) (by omega) (by omega)
  have act := Definable.active (N := N) (n := n + 1) (i := 0) (by omega)
  have point := Definable.atom (S := N.square) (n := n + 1) (M.constant .J)
    (i := 0) (j := 0) (by omega) (by omega)
  have elements := Definable.boundedAll (S := N.square) (n := n + 1) (i := 0) (by omega) _
    (Definable.atom (S := N.square) (n := n + 2) (M.constant .J) (i := 0) (j := 0) (by omega) (by omega))
  exact Definable.all (hRank.implies (act.implies (point.and elements)))

theorem fixed_rank_when_no_inductive (no : ∀ a, N.square.activePoint a → ¬Internal.Inductive N.mem a)
    (a : V) (ord : N.Ordinal a) : N.RankFixed a := by
  classical
  let bound := N.succ a
  have ordBound := N.ordinal_succ ord
  have hSpec := N.rank_fixed_definable (n := 2) (i := 0) (by decide)
  have induction_ := N.order_induction (a := bound) ordBound.ordered [] hSpec
  apply induction_ _ a ((N.mem_succ a a).mpr (Or.inr rfl))
  intro b onBound ih v vb dV
  have form : b = N.empty ∨ ∃ c, b = N.succ c := by
    by_cases zero : b = N.empty
    · exact Or.inl zero
    · by_cases succ : ∃ c, b = N.succ c
      · exact Or.inr succ
      · have active : N.square.activePoint b := active_subset N.laws dV (N.rank_contains_ordinal vb)
        exact (no b active (N.limit_is_inductive vb.1 zero succ)).elim
  let stage : N.Active := ⟨v, dV⟩
  rcases form with empty | ⟨c, next⟩
  · subst b
    have value := N.rank_empty vb
    have hasNone : Internal.Empty N.mem v := (N.empty_unique v).mpr value
    exact ⟨(N.fixed_iff_self_edge stage).mp (N.fixes_empty stage hasNone),
      fun x hx => (hasNone x hx).elim⟩
  · subst b
    have earlier : N.mem c (N.succ c) := (N.mem_succ _ _).mpr (Or.inr rfl)
    have ordC : N.Ordinal c := vb.1.of_mem N.toSetContext earlier
    obtain ⟨w, rankW⟩ := N.rank_exists ordC
    have wIn := N.rank_member rankW vb earlier
    let previous : N.Active := ⟨w, active_transitive N.laws dV wIn⟩
    have prev := ih c (ordBound.transitive (N.succ c) onBound c earlier) earlier w rankW previous.property
    have previousFix := (N.fixed_iff_self_edge previous).mpr prev.1
    have previousElement (x : N.Active) (hx : N.localMem x previous) : N.embedding x = x :=
      (N.fixed_iff_self_edge x).mpr (prev.2 x.val hx)
    have power : v = N.power w := N.rank_successor rankW vb
    refine ⟨(N.fixed_iff_self_edge stage).mp (Subtype.ext ?_), fun x hx => ?_⟩
    · have image := (N.preserves_power previous stage).mp power
      rw [previousFix] at image
      exact image.trans power.symm
    · let member : N.Active := ⟨x, active_transitive N.laws dV hx⟩
      have inside : N.Subset x w := (N.mem_power w x).mp (power ▸ hx)
      exact (N.fixed_iff_self_edge member).mp (N.fixes_subsets previous previousFix previousElement member inside)

/-- Nontriviality forces an inductive set in the active domain itself. -/
theorem active_inductive_exists : ∃ a, N.square.activePoint a ∧ Internal.Inductive N.mem a := by
  apply Classical.byContradiction
  intro no
  have absent (a : V) (ha : N.square.activePoint a) : ¬Internal.Inductive N.mem a :=
    fun h => no ⟨a, ha, h⟩
  obtain ⟨x, y, jxy, moved⟩ := N.movement
  have act := (j_active N.laws N.active_closure jxy).1
  obtain ⟨height, stage, rank, inside, xIn⟩ := N.active_rank act
  have fixed := (N.fixed_rank_when_no_inductive absent height rank.1 stage rank inside).2 x xIn
  exact moved (j_single_valued N.laws N.active_closure fixed jxy)

end NamedModel


namespace NamedModel

variable (N : NamedModel M V)

theorem active_omega_exists : ∃ w, N.square.activePoint w ∧ Internal.Omega N.mem w := by
  obtain ⟨start, active, inductiveSet⟩ := N.active_inductive_exists
  have described := Definable.all ((Definable.inductiveSet (N := N.toSetContext)
    (n := 3) (i := 0) (by decide)).implies
    (Definable.mem (N := N.toSetContext) (n := 3) (i := 1) (j := 0) (by decide) (by decide)))
  obtain ⟨w, spec⟩ := N.separate [] described start start
  have sub : N.Subset w start := fun x hx => ((spec x).mp hx).1
  refine ⟨w, active_subset N.laws active sub, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · have zero (a : V) (h : Internal.Inductive N.mem a) : N.mem N.empty a := by
      obtain ⟨z, hz, belongs⟩ := h.1
      exact ((N.empty_unique z).mp hz) ▸ belongs
    exact ⟨N.empty, N.empty_mem, (spec N.empty).mpr ⟨zero start inductiveSet, zero⟩⟩
  · intro x hx
    have previous := (spec x).mp hx
    have next (a : V) (h : Internal.Inductive N.mem a) (xIn : N.mem x a) : N.mem (N.succ x) a := by
      obtain ⟨y, step, new⟩ := h.2 x xIn
      exact ((N.internal_succ x y).mp step) ▸ new
    exact ⟨N.succ x, N.mem_succ x, (spec (N.succ x)).mpr ⟨next start inductiveSet previous.1,
      fun a ha => next a ha (previous.2 a ha)⟩⟩
  · exact fun a ha x hx => ((spec x).mp hx).2 a ha

theorem fixed_omega (env : Nat → V) : eval N.mem fixedOmega env := by
  obtain ⟨w, _, spec⟩ := N.active_omega_exists
  refine ⟨w, ?_⟩
  simpa only [Internal.Omega, Internal.Inductive, Internal.Empty, Internal.Succ, iff_def, eval, pushValue] using spec

end NamedModel
end PalomarI3380.SquareRepresentation
