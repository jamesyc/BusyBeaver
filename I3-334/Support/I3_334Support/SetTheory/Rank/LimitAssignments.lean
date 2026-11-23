module
public import I3_334Support.SetTheory.Rank.RankLimit
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} {N : NamedModel M V}

theorem CriticalRun.common_stage {w heights stages : V} (run : N.CriticalRun w heights stages)
    (omega : Internal.Omega N.mem w) {i j a b : V}
    (ai : Internal.At N.mem stages i a) (bj : Internal.At N.mem stages j b) :
    ∃ k c, Internal.At N.mem stages k c ∧ Internal.ElementaryIncluded N.mem w a c ∧
      Internal.ElementaryIncluded N.mem w b c := by
  have ii := SetRecursion.at_domain run.stageSequence.functionOn ai
  have ji := SetRecursion.at_domain run.stageSequence.functionOn bj
  rcases (N.omega_ordinal omega).ordered.compare i j ii ji with before | eq | after
  · exact ⟨j,b,bj,run.pairwise omega j ji i a b (Or.inl before) ai bj,N.elementary_refl w b⟩
  · exact ⟨j,b,bj,run.pairwise omega j ji i a b (Or.inr eq) ai bj,N.elementary_refl w b⟩
  · exact ⟨i,a,ai,N.elementary_refl w a,run.pairwise omega i ii j b a (Or.inl after) bj ai⟩

theorem CriticalRun.bound_assignment {w heights stages limit : V}
    (run : N.CriticalRun w heights stages) (omega : Internal.Omega N.mem w)
    (covers : ∀ x, N.mem x limit → ∃ n stage, Internal.At N.mem stages n stage ∧ N.mem x stage) :
    ∀ arity, N.mem arity w → ∀ env, Internal.FunctionInto N.mem env arity limit →
      ∃ i stage, Internal.At N.mem stages i stage ∧ Internal.FunctionInto N.mem env arity stage := by
  have input := Definable.functionInto (N := N.toSetContext) (n := 5) (i := 0) (j := 1) (k := 3)
    (by decide) (by decide) (by decide)
  have output := Definable.functionInto (N := N.toSetContext) (n := 7) (i := 2) (j := 3) (k := 0)
    (by decide) (by decide) (by decide)
  have lookup := Definable.graphValue (N := N.toSetContext) (n := 7) (i := 6) (j := 1) (k := 0)
    (by decide) (by decide) (by decide)
  have desc := Definable.all (input.implies (Definable.ex (Definable.ex (lookup.and output))))
  apply N.omega_induction omega [limit,stages] desc w
  · intro env h
    obtain ⟨s, hs, _⟩ := run.stageSequence.functionOn.1 N.empty (N.omega_zero omega)
    exact ⟨N.empty,s,hs,h.1,fun x hx => (N.empty_mem x hx).elim⟩
  · intro arity hArity smaller env typed
    let trimmed := N.restrictGraph env arity
    have restriction := N.restricts_canonical env arity
    have sub : N.Subset arity (N.succ arity) := fun x hx => (N.mem_succ _ _).mpr (Or.inl hx)
    have reduced : Internal.FunctionInto N.mem trimmed arity limit :=
      ⟨N.restricts_function typed.1 sub restriction, fun x hx y hy =>
        typed.2 x (sub x hx) y ((N.restricts_value restriction).mp hy).2⟩
    obtain ⟨i,s,stage,context⟩ := smaller trimmed reduced
    have arityHere : N.mem arity (N.succ arity) := (N.mem_succ _ _).mpr (Or.inr rfl)
    obtain ⟨x, atX, unique⟩ := typed.1.1 arity arityHere
    obtain ⟨j,t,tStage,xt⟩ := covers x (typed.2 arity arityHere x atX)
    obtain ⟨k,u,above,hu,hu'⟩ := run.common_stage omega stage tStage
    refine ⟨k,u,above,typed.1,fun index domain value edge => ?_⟩
    rcases (N.mem_succ _ _).mp domain with earlier | eq
    · exact hu.1 value (context.2 index earlier value ((N.restricts_value restriction).mpr ⟨earlier,edge⟩))
    · subst index
      exact (unique value edge).symm ▸ hu'.1 x xt

end PalomarI3380.SquareRepresentation.NamedModel
