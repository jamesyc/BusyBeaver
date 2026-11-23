module
public import I3_334.Statement
public import I3_334Support.Logic.TapeFormulas
@[expose] public section

namespace PalomarI3334

open PalomarI3380.Logic

namespace MachineFormula

open PalomarI3380.Logic.SetFormula
open PalomarI3380.Logic.Internal (Move Numeral)

def stepRow (s t : Levels) (q : Fin 334) (read : Bool) : SetFormula :=
  let row := literal[2 * q.val + (if read then 1 else 0)]?.getD 0
  both (numeral q.val s.state) (move read (row / 2 % 2 == 1) (row % 2 == 1) (row / 4) s t)

def literalStep (s t : Levels) : SetFormula :=
  anyOf ((List.finRange 334).map fun q => either (stepRow s t q false) (stepRow s t q true))

def halts : SetFormula :=
  someSet fun n => someSet fun domain => someSet fun history => someSet fun origin =>
    someSet fun start => someSet fun finish =>
      allOf [natObject n, successor n domain, functionOn history domain, empty origin,
        configCode ⟨origin, origin, origin⟩ start, graphValue history origin start,
        graphValue history n finish,
        someConfig fun final => both (configCode final finish) (numeral 334 final.state),
        eachIn n fun i => someSet fun next => someConfig fun s => someConfig fun t =>
          someSet fun before => someSet fun after =>
            allOf [successor i next, graphValue history i before, graphValue history next after,
              configCode s before, configCode t after, literalStep s t]]

variable {V : Type} {E : V → V → Prop} {d : Nat} {env : Nat → V} {default : V}

theorem holds_literalStep {s t : Levels} (hs : inScope d s) (ht : inScope d t) :
    holds E (literalStep s t) d env default ↔
      Internal.LiteralStep E (levelValue env s) (levelValue env t) := by
  rw [literalStep, holds_anyOf]
  have row (q : Fin 334) (read : Bool) :
      holds E (stepRow s t q read) d env default ↔ Numeral E q.val (env s.state) ∧
        let row := literal[2 * q.val + (if read then 1 else 0)]?.getD 0
        Move E read (row / 2 % 2 == 1) (row % 2 == 1) (row / 4)
          (levelValue env s) (levelValue env t) := by
    simp only [stepRow, holds_both, holds_numeral _ hs.1, holds_move _ _ _ _ hs ht]
  constructor
  · rintro ⟨f, hf, h⟩
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hf
    rcases (holds_either _ _).mp h with h | h
    · exact ⟨q, (row q false |>.mp h).1, false, (row q false |>.mp h).2⟩
    · exact ⟨q, (row q true |>.mp h).1, true, (row q true |>.mp h).2⟩
  · rintro ⟨q, hq, read, h⟩
    refine ⟨_, List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩, (holds_either _ _).mpr ?_⟩
    cases read
    · exact Or.inl ((row q false).mpr ⟨hq, h⟩)
    · exact Or.inr ((row q true).mpr ⟨hq, h⟩)

private theorem scope_leftMove (write head : Bool) {d : Nat} {s t : Levels} {tail : Nat}
    (hs : inScope d s) (ht : inScope d t) (ha : tail < d) : Scoped d (leftMove write head s t tail) := by
  obtain ⟨_, hl, _⟩ := hs
  obtain ⟨_, hm, hn⟩ := ht
  simp (disch := omega) only [leftMove, allOf, scope_someSet, scope_both, scope_bitCons, scope_eq,
    scope_neg, scope_falsity, and_self]

private theorem scope_move (read write right : Bool) (next : Nat) {d : Nat} {s t : Levels}
    (hs : inScope d s) (ht : inScope d t) : Scoped d (move read write right next s t) := by
  obtain ⟨hsq, hsl, hsr⟩ := hs
  obtain ⟨htq, htl, htr⟩ := ht
  have hs' : inScope (d + 1) s := by unfold inScope; omega
  have ht' : inScope (d + 1) t := by unfold inScope; omega
  cases right <;>
    simp (disch := omega) only [move, allOf, scope_someSet, scope_both, scope_either,
      scope_bitCons, scope_numeral, scope_eq, scope_neg, scope_falsity, scope_leftMove _ _ hs' ht',
      Bool.false_eq_true, ↓reduceIte, and_self]

private theorem scope_literalStep {d : Nat} {s t : Levels} (hs : inScope d s) (ht : inScope d t) :
    Scoped d (literalStep s t) := by
  rw [literalStep, scope_anyOf]
  intro f hf
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hf
  simp only [scope_either, stepRow, scope_both, scope_numeral _ hs.1, scope_move _ _ _ _ hs ht, and_self]

set_option maxHeartbeats 3000000 in
/-- The set formula interprets as an internal finite computation, even in
a model with nonstandard natural numbers. -/
theorem holds_halts : holds E halts d env default ↔ Internal.Halts E := by
  simp (disch := first | omega | (simp only [inScope, PalomarI3380.Logic.Internal.Configuration.state,
      PalomarI3380.Logic.Internal.Configuration.left, PalomarI3380.Logic.Internal.Configuration.right]; omega)) only
    [halts, someConfig, allOf, holds_someSet, holds_both, holds_natObject, holds_successor,
      holds_functionOn, holds_empty, holds_configCode, holds_graphValue, holds_numeral,
      holds_eachIn, holds_literalStep, holds_neg, holds_falsity, not_false_eq_true, and_true,
      levelValue, assign_here, assign_earlier, Internal.Halts]
  constructor
  · rintro ⟨n, domain, history, zero, start, finish, hn, hd, hf, hz, hs, hstart, hfinish,
      ⟨q, l, r, hcode, hq⟩, steps⟩
    refine ⟨n, domain, history, zero, start, finish, hn, hd, hf, hz, hs, hstart, hfinish,
      ⟨⟨q, l, r⟩, hcode, hq⟩, fun i hi => ?_⟩
    obtain ⟨next, q, l, r, q', l', r', b, a, rest⟩ := steps i hi
    exact ⟨next, ⟨q, l, r⟩, ⟨q', l', r'⟩, b, a, rest⟩
  · rintro ⟨n, domain, history, zero, start, finish, hn, hd, hf, hz, hs, hstart, hfinish,
      ⟨⟨q, l, r⟩, hcode, hq⟩, steps⟩
    refine ⟨n, domain, history, zero, start, finish, hn, hd, hf, hz, hs, hstart, hfinish,
      ⟨q, l, r, hcode, hq⟩, fun i hi => ?_⟩
    obtain ⟨next, ⟨q, l, r⟩, ⟨q', l', r'⟩, b, a, rest⟩ := steps i hi
    exact ⟨next, q, l, r, q', l', r', b, a, rest⟩

theorem scope_halts (d : Nat) : Scoped d halts := by
  simp (disch := first | omega | (simp only [inScope, PalomarI3380.Logic.Internal.Configuration.state,
      PalomarI3380.Logic.Internal.Configuration.left, PalomarI3380.Logic.Internal.Configuration.right]; omega)) only
    [halts, someConfig, allOf, scope_someSet, scope_both, scope_natObject, scope_successor,
      scope_functionOn, scope_empty, scope_configCode, scope_graphValue, scope_numeral,
      scope_eachIn, scope_literalStep, scope_neg, scope_falsity, and_self]

end MachineFormula

def haltingSentence : Formula := MachineFormula.halts 0

/-- The halting sentence represents the literal 334-state table in
every model of ZFC + I3. -/
theorem haltingSentence_represents : RepresentsHalting haltingSentence := by
  refine ⟨MachineFormula.scope_halts 0, ?_⟩
  intro V E _ _ env
  exact (eval_congr_bound haltingSentence (MachineFormula.scope_halts 0)
    (t := SetFormula.assignment 0 env (env 0)) (fun i hi => by omega)).trans MachineFormula.holds_halts

end PalomarI3334
