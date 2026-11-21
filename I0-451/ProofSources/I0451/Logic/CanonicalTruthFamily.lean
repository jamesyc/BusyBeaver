module
public import I0451.Logic.TruthOperations

/-! Replace the relative representatives in the emitted sentence by a
canonical truth-set family defined inside the set-theory model. -/

@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

theorem traceMap_definable (U : V) : ℒₛₑₜ-function₁[V] (fun R : V => R ∩ U) := by
  definability

noncomputable def traceImage (U C : V) : V :=
  repl (fun R => R ∩ U) (traceMap_definable U) C

theorem mem_traceImage (U C T : V) :
    T ∈ traceImage U C ↔ ∃ R ∈ C, T = R ∩ U := repl_spec (traceMap_definable U)

theorem stepTrace_inter (g U i R S : V) :
    StepTrace g U i (R ∩ U) (S ∩ U) ↔ StepTrace g U i R S := by
  unfold StepTrace
  apply exists_congr
  intro h
  constructor
  · rintro ⟨mem, imp, agree⟩
    exact ⟨mem, fun inR => ((mem_inter_iff.mp (imp (mem_inter_iff.mpr ⟨inR, mem⟩))).1), agree⟩
  · rintro ⟨mem, imp, agree⟩
    exact ⟨mem, fun inR => mem_inter_iff.mpr ⟨imp (mem_inter_iff.mp inR).1, mem⟩, agree⟩

theorem traceImage_closed {d U C : V} (family : TruthSets E d U C) :
    ClosedFamily d U (traceImage U C) where
  subset := by
    intro R mem g inR
    obtain ⟨S, _, rfl⟩ := (mem_traceImage U C R).mp mem
    exact (mem_inter_iff.mp inR).2
  atom := by
    intro i k hi hk
    obtain ⟨R, inFamily, exactTrace⟩ := family.atom ⟨i, hi⟩ ⟨k, hk⟩
    refine (mem_traceImage U C _).mpr ⟨R, inFamily, mem_ext_iff.mpr fun g => ?_⟩
    rw [mem_inter_iff, mem_atomicSet]
    exact ⟨fun ⟨inU, atom⟩ => ⟨(exactTrace g inU).mpr atom, inU⟩,
      fun ⟨inR, inU⟩ => ⟨inU, (exactTrace g inU).mp inR⟩⟩
  step := by
    intro i R S hi hr hs
    obtain ⟨r, inR, rfl⟩ := (mem_traceImage U C R).mp hr
    obtain ⟨s, inS, rfl⟩ := (mem_traceImage U C S).mp hs
    obtain ⟨W, inFamily, exactTrace⟩ := family.close ⟨i, hi⟩ r s inR inS
    refine (mem_traceImage U C _).mpr ⟨W, inFamily, mem_ext_iff.mpr fun g => ?_⟩
    rw [mem_inter_iff, mem_stepSet, stepTrace_inter]
    exact ⟨fun ⟨inU, h⟩ => ⟨(exactTrace g inU).mpr h, inU⟩,
      fun ⟨inW, inU⟩ => ⟨inU, (exactTrace g inU).mp inW⟩⟩

theorem truthSets_same_universe {d U C : V} (family : TruthSets E d U C) :
    U = assignments d :=
  mem_ext_iff.mpr fun g => (family.codes g).trans (mem_universe d g).symm

def GeneratedComparison (d j : V) : Prop :=
  j ∈ assignments d ∧ ∃ e ∈ assignments d, (∀ x ∈ d, At E e x x) ∧
    ∀ R ∈ generated d (assignments d), e ∈ R → j ∈ R

theorem generatedComparison_iff (d j : V) :
    GeneratedComparison d j ↔
      ∃ U C, j ∈ U ∧ TruthSets E d U C ∧
        ∃ e ∈ U, (∀ x ∈ d, At E e x x) ∧ ∀ R ∈ C, e ∈ R → j ∈ R := by
  constructor
  · rintro ⟨inU, witness⟩
    exact ⟨assignments d, generated d (assignments d), inU, generated_truthSets d, witness⟩
  · rintro ⟨U, C, inU, family, e, inUe, diagonal, comparison⟩
    have same := truthSets_same_universe family
    subst U
    refine ⟨inU, e, inUe, diagonal, fun R present hasE => ?_⟩
    have projected := ((mem_generated R d (assignments d)).mp present).2 _
      (traceImage_closed family)
    obtain ⟨S, inC, rfl⟩ := (mem_traceImage _ C R).mp projected
    exact mem_inter_iff.mpr ⟨comparison S inC (mem_inter_iff.mp hasE).1, inU⟩

theorem generatedComparison_iff_identity (d j : V) :
    GeneratedComparison d j ↔ j ∈ assignments d ∧
      ∀ R ∈ generated d (assignments d), identity d ∈ R → j ∈ R := by
  constructor
  · rintro ⟨inside, e, eInside, diagonal, compare⟩
    refine ⟨inside, fun R hR hId => compare R hR ?_⟩
    have values (x : V) (hx : x ∈ d) (y : V) : At E (identity d) x y ↔ At E e x y := by
      rw [diagonal_at]
      refine ⟨fun ⟨_, eq⟩ => eq.symm ▸ diagonal x hx, fun read => ⟨hx, ?_⟩⟩
      obtain ⟨u, _, same⟩ := ((mem_universe d e).mp eInside).2 ⟨x, hx⟩
      exact (same y read).trans (same x (diagonal x hx)).symm
    exact (generated_respects_values hR (identity_mem_universe d) eInside values).mp hId
  · rintro ⟨inside, compares⟩
    exact ⟨inside, identity d, identity_mem_universe d,
      fun x hx => (diagonal_at d x x).mpr ⟨hx, rfl⟩, compares⟩

theorem berkeleyFormula_iff_generated :
    SetSentences.BerkeleyFormula E ↔
      ∃ a : V, ∀ d, SetSentences.Transitive E d → a ∈ d →
        ∃ j, (∃ x ∈ a, ¬ At E j x x) ∧ GeneratedComparison d j := by
  constructor
  · rintro ⟨a, witness⟩
    refine ⟨a, fun d transitive belongs => ?_⟩
    obtain ⟨j, U, C, inside, moves, family, identity⟩ := witness d transitive belongs
    exact ⟨j, moves, (generatedComparison_iff d j).mpr ⟨U, C, inside, family, identity⟩⟩
  · rintro ⟨a, witness⟩
    refine ⟨a, fun d transitive belongs => ?_⟩
    obtain ⟨j, moves, comparison⟩ := witness d transitive belongs
    obtain ⟨U, C, inside, family, identity⟩ := (generatedComparison_iff d j).mp comparison
    exact ⟨j, U, C, inside, moves, family, identity⟩

end I0451.Logic.SetAssignments
