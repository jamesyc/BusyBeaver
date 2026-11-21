module
public import I3_380.StageGrowth
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Manifest

variable {A Point : Type} {M : Algebra A} {S : SquareRepresentation M Point}

def Stage (S : SquareRepresentation M Point) (a : Point) : Prop :=
  S.rel (M.constant .S) a a

theorem stage_diagonal (hM : M.Models preceding) {x y : Point}
    (rel : S.rel (M.constant .S) x y) : x = y := by
  have law := hM defineStages (by simp [preceding]) (fun _ => M.constant .U)
  let choice := M.choice (M.constant .T)
  change M.constant .S = M.product (M.converse choice) choice at law
  rw [law, S.product] at rel
  obtain ⟨z, first, second⟩ := rel
  exact S.choice_functional hM _ ((S.converse _ _ _).mp first) second

theorem active_iff (hM : M.Models preceding) (x : Point) :
    S.activePoint x ↔
      ∃ a, S.rel (M.constant .E) x a ∧ S.Stage a ∧ S.activePoint a := by
  have law := hM domainClosed (by simp [preceding, retained]) (fun _ => M.constant .U)
  change M.constant .D = M.inf (M.constant .I)
    (M.product (M.product (M.constant .E) (M.inf (M.constant .S) (M.constant .D))) (M.constant .U)) at law
  have rel (a b : Point) : S.rel (M.inf (M.constant .I)
      (M.product (M.product (M.constant .E) (M.inf (M.constant .S) (M.constant .D))) (M.constant .U))) a b ↔
      a = b ∧ ∃ x y, S.rel (M.constant .E) a x ∧ S.rel (M.constant .S) x y ∧ S.rel (M.constant .D) x y := by
    simp only [Algebra.inf, S.meet, S.identity, S.product, S.universal, and_true]
    constructor
    · rintro ⟨same, y, x, e, es, ed⟩
      exact ⟨same, x, y, e, es, ed⟩
    · rintro ⟨same, x, y, e, es, ed⟩
      exact ⟨same, y, x, e, es, ed⟩
  have original : S.activePoint x ↔ S.rel (M.inf (M.constant .I)
      (M.product (M.product (M.constant .E) (M.inf (M.constant .S) (M.constant .D))) (M.constant .U))) x x :=
    Iff.of_eq (congrArg (fun t => S.rel t x x) law)
  rw [original, rel]
  constructor
  · rintro ⟨_, a, b, h₁, h₂, h₃⟩
    obtain rfl := stage_diagonal hM h₂
    exact ⟨a, h₁, h₂, h₃⟩
  · rintro ⟨a, h₁, h₂, h₃⟩
    exact ⟨rfl, a, a, h₁, h₂, h₃⟩

theorem active_transitive (hM : M.Models preceding) {x y : Point}
    (yActive : S.activePoint y) (edge : S.rel (M.constant .E) x y) :
    S.activePoint x := by
  obtain ⟨a, contained, stage, isActive⟩ := (active_iff hM y).mp yActive
  obtain ⟨b, earlier, earlierStage, inclusion⟩ := (S.stage_iff hM stage y).mp contained
  have parent : S.activePoint b := (active_iff hM b).mpr ⟨a, earlier, stage, isActive⟩
  exact (active_iff hM x).mpr ⟨b, (S.subset_iff hM y b).mp inclusion x edge, earlierStage, parent⟩

theorem active_subset (hM : M.Models preceding) {x y : Point} (active : S.activePoint y)
    (subset : ∀ z, S.rel (M.constant .E) z x → S.rel (M.constant .E) z y) :
    S.activePoint x := by
  obtain ⟨a, existing, stage, actA⟩ := (active_iff hM y).mp active
  obtain ⟨b, previous, stageB, subsetB⟩ := (S.stage_iff hM stage y).mp existing
  exact (active_iff hM x).mpr ⟨a, subsets_in_later_stage hM stage stageB previous
    (fun z hz => (S.subset_iff hM y b).mp subsetB z (subset z hz)), stage, actA⟩

theorem active_power (hM : M.Models preceding) {x power : Point}
    (active : S.activePoint x)
    (powerset : ∀ y, S.rel (M.constant .E) y power ↔
      ∀ z, S.rel (M.constant .E) z y → S.rel (M.constant .E) z x) :
    S.activePoint power := by
  obtain ⟨a, inStage, stage, actA⟩ := (active_iff hM x).mp active
  obtain ⟨b, earlier, stageB, sub⟩ := (S.stage_iff hM stage x).mp inStage
  apply active_subset hM actA
  intro y hy
  exact subsets_in_later_stage hM stage stageB earlier
    (fun z hz => (S.subset_iff hM x b).mp sub z ((powerset y).mp hy z hz))

end PalomarI3380.SquareRepresentation
