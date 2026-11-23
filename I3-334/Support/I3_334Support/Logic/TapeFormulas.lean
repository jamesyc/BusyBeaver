module
public import I3_334Support.Logic.SetScope
public import I3_334Support.Logic.Target
@[expose] public section

namespace PalomarI3380.Logic

namespace SetFormula

abbrev Levels := Internal.Configuration Nat

def inScope (d : Nat) (c : Levels) : Prop := c.state < d ∧ c.left < d ∧ c.right < d

def someConfig (body : Levels → SetFormula) : SetFormula :=
  someSet fun q => someSet fun l => someSet fun r => body ⟨q, l, r⟩

def levelValue {V : Type} (env : Nat → V) (c : Levels) : Internal.Configuration V :=
  ⟨env c.state, env c.left, env c.right⟩

def configCode (c : Levels) (code : Nat) : SetFormula :=
  allOf [natObject c.state, natObject c.left, natObject c.right,
    someSet fun tapes => both (orderedPair c.left c.right tapes) (orderedPair c.state tapes code)]

def leftMove (write head : Bool) (s t : Levels) (tail : Nat) : SetFormula :=
  someSet fun left => someSet fun middle =>
    allOf [bitCons head left s.left, eq t.left left,
      bitCons write tail middle, bitCons head middle t.right]

def move (read write right : Bool) (next : Nat) (s t : Levels) : SetFormula :=
  someSet fun tail =>
    allOf [bitCons read tail s.right, numeral next t.state,
      if right then both (bitCons write s.left t.left) (eq t.right tail)
      else either (leftMove write false s t tail) (leftMove write true s t tail)]

variable {V : Type} {E : V → V → Prop} {d : Nat} {env : Nat → V} {default : V}

theorem holds_configCode {c : Levels} {code : Nat} (hc : inScope d c) (hp : code < d) :
    holds E (configCode c code) d env default ↔ Internal.ConfigurationCode E (levelValue env c) (env code) := by
  obtain ⟨hq, hl, hr⟩ := hc
  simp (disch := omega) only [configCode, Internal.ConfigurationCode, levelValue, allOf, holds_both,
    holds_natObject, holds_someSet, holds_orderedPair, holds_neg, holds_falsity,
    not_false_eq_true, and_true, assign_here, assign_earlier]

private theorem holds_leftMove (write head : Bool) {s t : Levels} {tail : Nat}
    (hs : inScope d s) (ht : inScope d t) (ha : tail < d) :
    holds E (leftMove write head s t tail) d env default ↔
      ∃ left middle, Internal.BitCons E head left (env s.left) ∧ env t.left = left ∧
        Internal.BitCons E write (env tail) middle ∧ Internal.BitCons E head middle (env t.right) := by
  obtain ⟨_, hl, _⟩ := hs
  obtain ⟨_, hm, hn⟩ := ht
  simp (disch := omega) only [leftMove, allOf, holds_someSet, holds_both, holds_bitCons, holds_eq,
    holds_neg, holds_falsity, not_false_eq_true, and_true, assign_here, assign_earlier]

theorem holds_move (read write right : Bool) (next : Nat) {s t : Levels}
    (hs : inScope d s) (ht : inScope d t) :
    holds E (move read write right next s t) d env default ↔
      Internal.Move E read write right next (levelValue env s) (levelValue env t) := by
  obtain ⟨hsq, hsl, hsr⟩ := hs
  obtain ⟨htq, htl, htr⟩ := ht
  cases right with
  | true =>
    simp (disch := omega) only [move, Internal.Move, levelValue, allOf, ↓reduceIte,
      holds_someSet, holds_both, holds_bitCons, holds_numeral, holds_eq, holds_neg, holds_falsity,
      not_false_eq_true, and_true, assign_here, assign_earlier]
  | false =>
    have hs' : inScope (d + 1) s := by unfold inScope; omega
    have ht' : inScope (d + 1) t := by unfold inScope; omega
    simp (disch := omega) only [move, Internal.Move, levelValue, allOf, Bool.false_eq_true, ↓reduceIte,
      holds_someSet, holds_both, holds_bitCons, holds_numeral, holds_either, holds_leftMove _ _ hs' ht',
      holds_neg, holds_falsity, not_false_eq_true, and_true, assign_here, assign_earlier]
    constructor
    · rintro ⟨tail, hr, hn, moves⟩
      rcases moves with ⟨left, middle, h₁, h₂, h₃, h₄⟩ | ⟨left, middle, h₁, h₂, h₃, h₄⟩
      · exact ⟨tail, hr, hn, left, false, middle, h₁, h₂, h₃, h₄⟩
      · exact ⟨tail, hr, hn, left, true, middle, h₁, h₂, h₃, h₄⟩
    · rintro ⟨tail, hr, hn, left, head, middle, h₁, h₂, h₃, h₄⟩
      cases head
      · exact ⟨tail, hr, hn, Or.inl ⟨left, middle, h₁, h₂, h₃, h₄⟩⟩
      · exact ⟨tail, hr, hn, Or.inr ⟨left, middle, h₁, h₂, h₃, h₄⟩⟩

theorem scope_configCode {d : Nat} {c : Levels} {code : Nat}
    (hc : inScope d c) (hp : code < d) : Scoped d (configCode c code) := by
  obtain ⟨hq, hl, hr⟩ := hc
  simp (disch := omega) only [configCode, allOf, scope_both, scope_natObject, scope_someSet,
    scope_orderedPair, scope_neg, scope_falsity, and_self]

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

end SetFormula
end PalomarI3380.Logic
