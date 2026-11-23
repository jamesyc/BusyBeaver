module
public import I3_334Support.SetTheory.Rank.LocalElementarity
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Manifest

variable {A Point : Type} {M : Algebra A} {S : SquareRepresentation M Point}

theorem subsets_in_later_stage (hM : M.Models preceding) {a b x : Point}
    (later : S.rel (M.constant .S) a a) (earlier : S.rel (M.constant .S) b b)
    (inLater : S.rel (M.constant .E) b a)
    (subset : ∀ z, S.rel (M.constant .E) z x → S.rel (M.constant .E) z b) :
    S.rel (M.constant .E) x a :=
  (S.stage_iff hM later x).mpr ⟨b, inLater, earlier, (S.subset_iff hM x b).mpr subset⟩

/-- The ordinary diagonal subset excludes a represented injection of
all subsets of a set into that set. No well-foundedness of membership is
needed for this argument. -/
theorem cantor_no_injection (hM : M.Models preceding)
    (names : ∀ x, S.Named x) (set : Point) (graph : A)
    (maps : ∀ x, (∀ z, S.rel (M.constant .E) z x → S.rel (M.constant .E) z set) →
      ∃ m, S.rel (M.constant .E) m set ∧ S.rel graph x m)
    (injective : ∀ x y m, S.rel graph x m → S.rel graph y m → x = y) :
    False := by
  let E := M.constant .E
  let off := M.neg (M.product (M.converse graph) (M.converse E))
  let diagonal := M.inf (M.constant .I) off
  let test := M.product diagonal (M.constant .U)
  have property (x y : Point) : S.rel test x y ↔ ¬ ∃ z, S.rel graph z x ∧ S.rel E x z := by
    change S.rel (M.product (M.neg (M.nand (M.constant .I) off)) (M.constant .U)) x y ↔ _
    rw [S.product]
    simp only [S.meet, S.identity, S.universal, and_true, exists_eq_left', off, S.complement,
      S.product, S.converse]
  obtain ⟨w, spec⟩ := S.separate_column hM test set (names set)
  have subsets : ∀ z, S.rel E z w → S.rel E z set := fun z h => ((spec z).mp h).1
  obtain ⟨m, member, output⟩ := maps w subsets
  have contradictionAt : S.rel E m w ↔ ¬S.rel E m w := by
    have test := (spec m).trans (and_congr_right fun _ => property m set)
    constructor
    · intro both
      intro inSet
      exact (test.mp both).2 ⟨w, output, inSet⟩
    · intro absent
      refine test.mpr ⟨member, ?_⟩
      rintro ⟨z, hz, inside⟩
      have same := injective z w m hz output
      exact absent (same ▸ inside)
  have absent : ¬S.rel E m w := fun h => contradictionAt.mp h h
  exact absent (contradictionAt.mpr absent)

theorem no_stage_contraction (hM : M.Models preceding) (names : ∀ x, S.Named x)
    {a b : Point} (ha : S.rel (M.constant .S) a a) (hb : S.rel (M.constant .S) b b)
    (edge : S.rel (M.constant .E) b a) (graph : A)
    (maps : ∀ x, S.rel (M.constant .E) x a → ∃ y, S.rel (M.constant .E) y b ∧ S.rel graph x y)
    (inj : ∀ x y z, S.rel graph x z → S.rel graph y z → x = y) : False :=
  cantor_no_injection hM names b graph
    (fun x h => maps x (subsets_in_later_stage hM ha hb edge h)) inj

end PalomarI3380.SquareRepresentation
