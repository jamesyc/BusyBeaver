module
public import I0451.Logic.TruthSupport

/-! On a domain containing the natural labels, the literal closure
operation yields the ordinary conjunction, negation and quantifiers
on assignment truth sets. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode
open I0451.Logic.ZFModel (common_nat_bound avoid_nat_label)

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

theorem SameExcept.of_agree {d i g h : V} (hi : i ∈ d) (gU : g ∈ assignments d) (hU : h ∈ assignments d)
    (agree : Agree E i g h) : SameExcept d i g h := by
  let ops := ZFModel.setOperations (V := V)
  obtain ⟨f, gCode⟩ := (is_map_iff_encodes ops).mp ((mem_universe _ _).mp gU)
  obtain ⟨k, hCode⟩ := (is_map_iff_encodes ops).mp ((mem_universe _ _).mp hU)
  intro x hx different y
  let label : Domain E d := ⟨x, hx⟩
  let changed : Domain E d := ⟨i, hi⟩
  have differentLabel : label ≠ changed := fun eq => different (congrArg Subtype.val eq)
  have keep := agree.preserves ops gCode hCode differentLabel
  exact (gCode.at_iff label y).trans ((by rw [keep] :
    (f label).val = y ↔ (k label).val = y).trans (hCode.at_iff label y).symm)

theorem replace_assignment_value {d g i value : V} (gU : g ∈ assignments d)
    (iD : i ∈ d) (valueD : value ∈ d) :
    ∃ h ∈ assignments d, At E h i value ∧ Agree E i g h := by
  classical
  let ops := ZFModel.setOperations (V := V)
  let label : Domain E d := ⟨i, iD⟩
  obtain ⟨f, code⟩ := (is_map_iff_encodes ops).mp ((mem_universe d g).mp gU)
  obtain ⟨h, changed, stays⟩ := code.replace ops label ⟨value, valueD⟩
  refine ⟨h, (mem_universe d h).mpr ((is_map_iff_encodes ops).mpr ⟨_, changed⟩), ?_, stays⟩
  exact (changed.at_iff label _).mpr (by simp [Identity.replace])

theorem generated_respects_values {d R g h : V}
    (has : R ∈ generated d (assignments d)) (gU : g ∈ assignments d) (hU : h ∈ assignments d)
    (values : ∀ x ∈ d, ∀ y, At E g x y ↔ At E h x y) :
    g ∈ R ↔ h ∈ R := by
  obtain ⟨n, hn, ignores⟩ := generated_hasClockBound d R has
  exact ignores n hn (mem_irrefl n) g gU h hU (fun x hx _ => values x hx)

theorem generated_empty {d : V} (omega : (ω : V) ⊆ d) :
    (∅ : V) ∈ generated d (assignments d) := by
  let i : Domain E d := ⟨0, omega 0 zero_mem_ω⟩
  have eq : atomicSet (assignments d) i.val i.val = ∅ := by
    apply mem_ext_iff.mpr
    intro g
    constructor
    · intro member
      obtain ⟨gU, atom⟩ := (mem_atomicSet _ _ _ _).mp member
      obtain ⟨y, found, _⟩ := ((mem_universe d g).mp gU).2 i
      exact (mem_irrefl y (atom y y found found)).elim
    · simp
  rw [← eq]
  exact (generated_closed d _).atom i.val i.val i.property i.property

theorem generated_implication {d R S : V} (omega : (ω : V) ⊆ d)
    (rMem : R ∈ generated d (assignments d)) (sMem : S ∈ generated d (assignments d)) :
    ∃ T ∈ generated d (assignments d), ∀ g ∈ assignments d, g ∈ T ↔ (g ∈ R → g ∈ S) := by
  obtain ⟨first, firstNat, left⟩ := generated_hasClockBound d R rMem
  obtain ⟨second, secondNat, right⟩ := generated_hasClockBound d S sMem
  obtain ⟨n, hn, hasR, hasS⟩ := common_nat_bound first second firstNat secondNat
  have readyR := left n hn (fun h => mem_irrefl n (hasR n h))
  have readyS := right n hn (fun h => mem_irrefl n (hasS n h))
  have index := omega n hn
  let U := assignments d
  refine ⟨stepSet U n R S, (generated_closed d U).step n R S index rMem sMem, fun g gU => ?_⟩
  rw [mem_stepSet, and_iff_right gU]
  constructor
  · rintro ⟨h, hU, step, change⟩ premise
    have same := SameExcept.of_agree index gU hU change
    exact (readyS g gU h hU same).mpr (step ((readyR g gU h hU same).mp premise))
  · intro conditional
    exact ⟨g, gU, conditional, fun p gp ngp => (ngp gp).elim⟩

theorem generated_negation {d R : V} (omega : (ω : V) ⊆ d)
    (rMem : R ∈ generated d (assignments d)) :
    ∃ T ∈ generated d (assignments d), ∀ g ∈ assignments d, g ∈ T ↔ g ∉ R := by
  obtain ⟨T, tMem, spec⟩ := generated_implication omega rMem (generated_empty omega)
  exact ⟨T, tMem, fun g gU => by simpa using spec g gU⟩

theorem generated_full {d : V} (omega : (ω : V) ⊆ d) :
    assignments d ∈ generated d (assignments d) := by
  obtain ⟨T, tMem, spec⟩ := generated_negation omega (generated_empty omega)
  have eq : T = assignments d := by
    apply mem_ext_iff.mpr
    intro g
    exact ⟨(generated_closed d _).subset T tMem g, fun gU => (spec g gU).mpr (by simp)⟩
  exact eq ▸ tMem

theorem generated_existential {d R i : V} (omega : (ω : V) ⊆ d) (di : i ∈ d)
    (rMem : R ∈ generated d (assignments d)) :
    ∃ T ∈ generated d (assignments d), ∀ g ∈ assignments d, g ∈ T ↔
      ∃ h ∈ assignments d, h ∈ R ∧ SameExcept d i g h := by
  classical
  let U := assignments d
  let index : Domain E d := ⟨i, di⟩
  refine ⟨stepSet U i U R, (generated_closed d U).step i U R di (generated_full omega) rMem, fun g gU => ?_⟩
  rw [mem_stepSet, and_iff_right gU]
  constructor
  · rintro ⟨h, hU, yes, change⟩
    exact ⟨h, hU, yes hU, SameExcept.of_agree di gU hU change⟩
  · rintro ⟨h, hU, yes, agree⟩
    let ops := ZFModel.setOperations (V := V)
    obtain ⟨f, gCode⟩ := (is_map_iff_encodes ops).mp ((mem_universe _ _).mp gU)
    obtain ⟨p, hCode⟩ := (is_map_iff_encodes ops).mp ((mem_universe _ _).mp hU)
    obtain ⟨u, uCode, changed⟩ := gCode.replace ops index (p index)
    have uU : u ∈ U := (mem_universe d _).mpr ((is_map_iff_encodes ops).mpr ⟨_, uCode⟩)
    have equalMaps : Identity.replace f index (p index) = p := by
      funext x
      by_cases same : x = index
      · simp [Identity.replace, same]
      · have notI : x.val ≠ i := fun eq => same (Subtype.ext eq)
        have value := decoded_eq gCode hCode agree x notI
        simp [Identity.replace, same, value]
    rw [equalMaps] at uCode
    have reads (x : V) (hx : x ∈ d) (y : V) : At E h x y ↔ At E u x y :=
      (hCode.at_iff ⟨x, hx⟩ y).trans (uCode.at_iff ⟨x, hx⟩ y).symm
    exact ⟨u, uU, fun _ => (generated_respects_values rMem hU uU reads).mp yes, changed⟩

theorem generated_conjunction {d R S : V} (omega : (ω : V) ⊆ d)
    (rMem : R ∈ generated d (assignments d)) (sMem : S ∈ generated d (assignments d)) :
    ∃ T ∈ generated d (assignments d), ∀ g ∈ assignments d, g ∈ T ↔ g ∈ R ∧ g ∈ S := by
  classical
  obtain ⟨notS, hasNotS, notSpec⟩ := generated_negation omega sMem
  obtain ⟨imp, hasImp, impSpec⟩ := generated_implication omega rMem hasNotS
  obtain ⟨T, tMem, tSpec⟩ := generated_negation omega hasImp
  exact ⟨T, tMem, fun g gU => by
    rw [tSpec g gU, impSpec g gU, notSpec g gU]
    simp⟩

theorem generated_biconditional {d R S : V} (omega : (ω : V) ⊆ d)
    (rMem : R ∈ generated d (assignments d)) (sMem : S ∈ generated d (assignments d)) :
    ∃ T ∈ generated d (assignments d), ∀ g ∈ assignments d, g ∈ T ↔ (g ∈ R ↔ g ∈ S) := by
  obtain ⟨forward, inF, fSpec⟩ := generated_implication omega rMem sMem
  obtain ⟨backward, inB, bSpec⟩ := generated_implication omega sMem rMem
  obtain ⟨T, tMem, tSpec⟩ := generated_conjunction omega inF inB
  refine ⟨T, tMem, fun g gU => ?_⟩
  rw [tSpec g gU, fSpec g gU, bSpec g gU]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem generated_universal {d R i : V} (omega : (ω : V) ⊆ d) (di : i ∈ d)
    (rMem : R ∈ generated d (assignments d)) :
    ∃ T ∈ generated d (assignments d), ∀ g ∈ assignments d, g ∈ T ↔
      ∀ h ∈ assignments d, SameExcept d i g h → h ∈ R := by
  classical
  obtain ⟨notR, inNot, notSpec⟩ := generated_negation omega rMem
  obtain ⟨someNot, inSome, someSpec⟩ := generated_existential omega di inNot
  obtain ⟨T, inT, tSpec⟩ := generated_negation omega inSome
  refine ⟨T, inT, fun g gU => ?_⟩
  rw [tSpec g gU, someSpec g gU]
  constructor
  · intro noWitness h hU same
    by_contra failed
    exact noWitness ⟨h, hU, (notSpec h hU).mpr failed, same⟩
  · rintro all ⟨h, hU, negation, same⟩
    exact (notSpec h hU).mp negation (all h hU same)

end I0451.Logic.SetAssignments
