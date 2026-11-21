module
public import I3_380.RecursionAgreement
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetRecursion

open Logic

variable {A V : Type} {M : Algebra A} {N : SetContext M V} (R : SetRecursion N)

theorem at_domain {f a x y : V} (hf : Internal.FunctionOn N.mem f a)
    (h : Internal.At N.mem f x y) : N.mem x a := by
  obtain ⟨p, hp, pair⟩ := h
  obtain ⟨u, v, dom, code⟩ := hf.2 p hp
  exact (Internal.orderedPair_injective code pair).1 ▸ dom

theorem full_family (a : V) (initial : R.Initial a) :
    ∃ family, ∀ f, N.mem f family ↔ ∃ x, N.mem x a ∧ R.FullSolution x f := by
  let params := [R.domain, R.orderKey, R.updateKey]
  obtain ⟨P, scope, formula⟩ := R.full_solution_definable (n := 5) (d := 2) (o := 3) (u := 4) (x := 0) (f := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have shape (x f : V) :
      RelationFormula.eval N.square P (parameterEnv params x f) ↔ R.FullSolution x f := by
    refine (formula _).trans ?_
    change (∃ b, R.IsThrough x b ∧ Internal.FunctionOn N.mem f b ∧
      (∀ y, N.mem y b → ∃ cut prior value, R.IsCut y cut ∧ N.Restricts f cut prior ∧
        Internal.At N.mem f y value ∧ R.update R.updateKey y prior value)) ↔ _
    exact ⟨fun ⟨b, h, funOn, eq⟩ => ⟨b, h, ⟨funOn, eq⟩⟩, fun ⟨b, h, sol⟩ =>
      ⟨b, h, sol.functionOn, sol.agrees⟩⟩
  let onDomain := RelationFormula.and (.atom (M.constant .E) 0 2) P
  have hBound : onDomain.Bound (params.length + 2) := by
    change (0 < 5 ∧ 2 < 5) ∧ P.Bound 5
    exact ⟨⟨by decide, by decide⟩, scope⟩
  have precise (x f : V) :
      RelationFormula.eval N.square onDomain (parameterEnv params x f) ↔
        N.mem x R.domain ∧ R.FullSolution x f :=
    and_congr_right fun _ => shape x f
  obtain ⟨family, spec⟩ := N.replaces params onDomain hBound
    (fun x y z hy hz =>
      R.full_solution_unique ((precise x y).mp hy).1 ((precise x y).mp hy).2 ((precise x z).mp hz).2) a
  refine ⟨family, fun f => (spec f).trans ?_⟩
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, ((precise x f).mp h).2⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, (precise x f).mpr ⟨initial.1 x hx, h⟩⟩

/-- The union of all compatible initial graph approximations is a
solution on the covered initial segment. -/
theorem gather_solutions (a : V) (initial : R.Initial a)
    (available : ∀ x, N.mem x a → ∃ f, R.FullSolution x f) :
    ∃ graph, R.Solution a graph := by
  obtain ⟨family, parts⟩ := R.full_family a initial
  let graph := N.union family
  have value (x y : V) :
      Internal.At N.mem graph x y ↔ ∃ f, N.mem f family ∧ Internal.At N.mem f x y := by
    simp only [N.at_pair, graph, N.mem_union]
  have piece {f : V} (hf : N.mem f family) :
      ∃ b, R.Initial b ∧ N.Subset b a ∧ R.Solution b f := by
    obtain ⟨start, startIn, b, through, sol⟩ := (parts f).mp hf
    exact ⟨b, R.through_initial (initial.1 _ startIn) through, R.through_in_initial startIn initial through, sol⟩
  have forPoint {x : V} (hx : N.mem x a) :
      ∃ f b, N.mem f family ∧ N.mem x b ∧ R.Initial b ∧ R.Solution b f := by
    obtain ⟨f, b, cut, sol⟩ := available x hx
    exact ⟨f, b, (parts f).mpr ⟨x, hx, b, cut, sol⟩,
      (cut x).mpr ⟨initial.1 _ hx, Or.inr rfl⟩, R.through_initial (initial.1 _ hx) cut, sol⟩
  have agrees {f b x y : V} (hf : N.mem f family) (ib : R.Initial b) (sol : R.Solution b f)
      (hx : N.mem x b) : Internal.At N.mem graph x y ↔ Internal.At N.mem f x y := by
    constructor
    · intro h
      obtain ⟨g, hg, out⟩ := (value x y).mp h
      obtain ⟨c, initC, subC, other⟩ := piece hg
      have found := at_domain other.functionOn out
      exact (R.solutions_agree initC ib other sol found hx).mp out
    · exact fun atF => (value x y).mpr ⟨f, hf, atF⟩
  refine ⟨graph, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro x hx
    obtain ⟨f, b, hf, xb, ib, sol⟩ := forPoint hx
    obtain ⟨y, atF, unique⟩ := sol.functionOn.1 x xb
    exact ⟨y, (agrees hf ib sol xb).mpr atF, fun z atG =>
      unique z ((agrees hf ib sol xb).mp atG)⟩
  · intro p hp
    obtain ⟨f, hf, inF⟩ := (N.mem_union family p).mp hp
    obtain ⟨b, ib, sub, sol⟩ := piece hf
    obtain ⟨x, y, xb, pair⟩ := sol.functionOn.2 p inF
    exact ⟨x, y, sub x xb, pair⟩
  · intro x hx
    obtain ⟨f, b, hf, xb, ib, sol⟩ := forPoint hx
    obtain ⟨cut, prior, result, hcut, prev, v, update⟩ := sol.agrees x xb
    have cutB := R.cut_in_initial xb ib hcut
    have restriction : N.Restricts graph cut prior := by
      intro p
      rw [prev p]
      constructor
      · rintro ⟨member, coords⟩
        exact ⟨(N.mem_union _ _).mpr ⟨f, hf, member⟩, coords⟩
      · rintro ⟨hp, z, hz, y, pair⟩
        have code := (N.orderedPair_iff z y p).mp pair
        subst p
        have same := agrees (x := z) (y := y) hf ib sol (cutB z hz)
        have inF : N.mem (N.orderedPair z y) f :=
          (N.at_pair _ _ _).mp (same.mp ((N.at_pair _ _ _).mpr hp))
        exact ⟨inF, z, hz, y, N.orderedPair_intro z y⟩
    exact ⟨cut, prior, result, hcut, restriction, (agrees hf ib sol xb).mpr v, update⟩

end PalomarI3380.SquareRepresentation.SetRecursion
