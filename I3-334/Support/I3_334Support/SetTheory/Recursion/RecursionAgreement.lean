module
public import I3_334Support.SetTheory.Recursion.SetRecursion
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetRecursion

open Logic

variable {A V : Type} {M : Algebra A} {N : SetContext M V} (R : SetRecursion N)

theorem solution_definable {n d o u s f : Nat}
    (hd : d < n) (ho : o < n) (hu : u < n) (hs : s < n) (hf : f < n) :
    N.square.Definable n (fun env => Internal.FunctionOn N.mem (env f) (env s) ∧
      ∀ x, N.mem x (env s) → ∃ cut prior value,
        (∀ y, N.mem y cut ↔ N.mem y (env d) ∧ R.order (env o) y x) ∧
        N.Restricts (env f) cut prior ∧ Internal.At N.mem (env f) x value ∧
        R.update (env u) x prior value) := by
  have cut := R.cut_definable (n := n + 4) (i := d + 4) (j := o + 4) (k := 3) (l := 2)
    (by omega) (by omega) (by omega) (by omega)
  have previous := Definable.restricts (N := N) (n := n + 4) (i := f + 4) (j := 2) (k := 1)
    (by omega) (by omega) (by omega)
  have value := Definable.graphValue (N := N) (n := n + 4) (i := f + 4) (j := 3) (k := 0)
    (by omega) (by omega) (by omega)
  have updated := R.update_formula (n := n + 4) (i := u + 4) (j := 3) (k := 1) (l := 0)
    (by omega) (by omega) (by omega) (by omega)
  have existsLocally := Definable.ex (Definable.ex (Definable.ex
    (cut.and (previous.and (value.and updated)))))
  exact (Definable.functionOn hf hs).and (Definable.boundedAll hs _ existsLocally)

theorem full_solution_definable {n d o u x f : Nat}
    (hd : d < n) (ho : o < n) (hu : u < n) (hx : x < n) (hf : f < n) :
    N.square.Definable n (fun env => ∃ segment,
      (∀ y, N.mem y segment ↔ N.mem y (env d) ∧ (R.order (env o) y (env x) ∨ y = env x)) ∧
      Internal.FunctionOn N.mem (env f) segment ∧
      ∀ a, N.mem a segment → ∃ cut prior value,
        (∀ y, N.mem y cut ↔ N.mem y (env d) ∧ R.order (env o) y a) ∧
        N.Restricts (env f) cut prior ∧ Internal.At N.mem (env f) a value ∧
        R.update (env u) a prior value) :=
  Definable.ex ((R.through_definable (i := d + 1) (j := o + 1) (k := x + 1) (l := 0)
    (by omega) (by omega) (by omega) (by omega)).and
    (R.solution_definable (d := d + 1) (o := o + 1) (u := u + 1) (s := 0) (f := f + 1)
      (by omega) (by omega) (by omega) (by omega) (by omega)))

private theorem differences_exist (a f g : V) :
    ∃ diff, ∀ x, N.mem x diff ↔ N.mem x a ∧
      ∃ y, Internal.At N.mem f x y ∧ ¬ Internal.At N.mem g x y :=
  N.separate [f, g] (Definable.ex
    ((Definable.graphValue (N := N) (n := 5) (i := 3) (j := 1) (k := 0)
      (by decide) (by decide) (by decide)).and
      (Definable.not (Definable.graphValue (N := N) (n := 5) (i := 4) (j := 1) (k := 0)
        (by decide) (by decide) (by decide))))) a a

theorem solution_unique {a f g : V} (init : R.Initial a) (hf : R.Solution a f) (hg : R.Solution a g) :
    f = g := by
  classical
  obtain ⟨diff, split⟩ := differences_exist (N := N) a f g
  have noDiff : ¬N.NonemptySet diff := by
    intro hd
    have sub : N.Subset diff R.domain := fun x hx => init.1 x ((split x).mp hx).1
    obtain ⟨x, hx, least⟩ := R.wellOrder.least diff sub hd
    obtain ⟨ha, y, hy, notG⟩ := (split x).mp hx
    obtain ⟨cut, pf, yf, hCut, fPrefix, fAt, fUpdate⟩ := hf.agrees x ha
    obtain ⟨cut', pg, yg, hCut', gPrefix, gAt, gUpdate⟩ := hg.agrees x ha
    cases R.cut_eq hCut hCut'
    have cutIn := R.cut_in_initial ha init hCut
    have priorSame : pf = pg := by
      apply N.function_ext (N.restricts_function hf.functionOn cutIn fPrefix)
        (N.restricts_function hg.functionOn cutIn gPrefix)
      intro z value hz
      rw [N.restricts_value fPrefix, N.restricts_value gPrefix]
      have notDiff : ¬N.mem z diff := by
        intro hzDiff
        obtain ⟨dom, pred⟩ := (hCut z).mp hz
        rcases least z hzDiff with eq | after
        · exact R.wellOrder.irrefl x (sub x hx) (eq ▸ pred)
        · exact SetContext.WellOrderOn.asymm N R.wellOrder dom (sub x hx) pred after
      have transferred (v : V) (h : Internal.At N.mem f z v) : Internal.At N.mem g z v :=
        Classical.byContradiction fun missing => notDiff ((split z).mpr ⟨cutIn z hz, v, h, missing⟩)
      refine and_congr_right fun hz => ⟨transferred value, fun gv => ?_⟩
      obtain ⟨v, hv, _⟩ := hf.functionOn.1 z (cutIn z hz)
      obtain ⟨w, hw, one⟩ := hg.functionOn.1 z (cutIn z hz)
      have same := (one v (transferred v hv)).trans (one value gv).symm
      exact same ▸ hv
    cases priorSame
    have same := R.update_unique x pf yf yg fUpdate gUpdate
    have unique := (hf.functionOn.1 x ha)
    obtain ⟨v, hv, one⟩ := unique
    have matchY := (one y hy).trans (one yf fAt).symm
    exact notG ((matchY.trans same).symm ▸ gAt)
  apply N.function_ext hf.functionOn hg.functionOn
  intro x y hx
  have transfer (y : V) (hf : Internal.At N.mem f x y) : Internal.At N.mem g x y :=
    Classical.byContradiction fun missing => noDiff ⟨x, (split x).mpr ⟨hx, y, hf, missing⟩⟩
  refine ⟨transfer y, fun h => ?_⟩
  obtain ⟨z, hz, _⟩ := hf.functionOn.1 x hx
  obtain ⟨w, hw, one⟩ := hg.functionOn.1 x hx
  exact ((one z (transfer z hz)).trans (one y h).symm) ▸ hz

theorem full_solution_unique {x f g : V} (xIn : N.mem x R.domain)
    (hf : R.FullSolution x f) (hg : R.FullSolution x g) : f = g := by
  obtain ⟨a, rangeF, fSol⟩ := hf
  obtain ⟨b, rangeG, gSol⟩ := hg
  have same := R.through_eq rangeF rangeG
  subst b
  exact R.solution_unique (R.through_initial xIn rangeF) fSol gSol

theorem solutions_agree {a b f g : V} (initA : R.Initial a) (initB : R.Initial b)
    (hf : R.Solution a f) (hg : R.Solution b g) {x y : V}
    (ha : N.mem x a) (hb : N.mem x b) :
    Internal.At N.mem f x y ↔ Internal.At N.mem g x y := by
  let sub := N.inter a b
  let f' := N.restrictGraph f sub
  let g' := N.restrictGraph g sub
  have fa := N.restricts_canonical f sub
  have gb := N.restricts_canonical g sub
  have init := R.initial_inter initA initB
  have aInc : N.Subset sub a := fun z hz => ((N.mem_inter _ _ _).mp hz).1
  have bInc : N.Subset sub b := fun z hz => ((N.mem_inter _ _ _).mp hz).2
  have same : f' = g' := R.solution_unique init
    (R.solution_restrict hf aInc init fa) (R.solution_restrict hg bInc init gb)
  have h : N.mem x sub := (N.mem_inter _ _ _).mpr ⟨ha, hb⟩
  constructor
  · intro value
    have carried : Internal.At N.mem f' x y := (N.restricts_value fa).mpr ⟨h, value⟩
    rw [same] at carried
    exact ((N.restricts_value gb).mp carried).2
  · intro value
    have carried : Internal.At N.mem g' x y := (N.restricts_value gb).mpr ⟨h, value⟩
    rw [← same] at carried
    exact ((N.restricts_value fa).mp carried).2

end PalomarI3380.SquareRepresentation.SetRecursion
