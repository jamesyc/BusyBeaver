module
public import I3_380.Engine.DecoderWalk
@[expose] public section

namespace PalomarI3380.Engine

structure LogicalState (V : Type := Nat) where
  path : List Bool
  registers : List V
  deriving DecidableEq, Repr

/-- Reading a continuation after an already successful decoder walk
changes only the unused suffix. -/
theorem follow_append {fuel q : Nat} {before input : List Bool} {d : Decoded}
    (h : follow fuel q before input = some d) (tail : List Bool) :
    follow fuel q before (input ++ tail) = some { d with rest := d.rest ++ tail } := by
  induction fuel generalizing q before input d with
  | zero => simp [follow] at h
  | succ fuel ih =>
    cases input with
    | nil => simp [follow] at h
    | cons b rest =>
      by_cases hChild : 0 < height (transition q b).target
      · simp only [follow, List.cons_append, hChild, ↓reduceIte] at h ⊢
        exact ih h
      · cases he : exitFor (transition q b).target with
        | none => simp [follow, hChild, he] at h
        | some op =>
          simp only [follow, hChild, ↓reduceIte, he, Option.map_some, Option.some.injEq] at h
          cases h
          simp only [follow, List.cons_append, hChild, ↓reduceIte, he, Option.map_some]

variable {V : Type} [OfNat V 0] [OfNat V 1] [Add V] [Sub V] [DecidableEq V]

def logicalDecoded (rs : List V) (d : Decoded) : Option (LogicalState V) :=
  match d.command with
  | .halt => none
  | .break skip => some ⟨(breakPath skip d.before).reverse, rs⟩
  | .continue false => some ⟨d.before.reverse, rs⟩
  | .continue true => some ⟨(stripThrough true d.before).reverse, rs⟩
  | .register dec r =>
    let index := rs.length - (r.val + 1)
    let value := rs[index]?.getD 0
    some ⟨(breakPath (zeroDecrement dec value) d.path.reverse).reverse,
      rs.set index (registerValue dec value)⟩

def logicalNext (s : LogicalState V) : Option (LogicalState V) :=
  (follow 59 Port.root [] (s.path ++ zeros 59)).bind (logicalDecoded s.registers)

private theorem logical_suffix (rs : List V) (d : Decoded) (rest : List Bool) :
    logicalDecoded rs { d with rest := rest } = logicalDecoded rs d := by
  cases d
  rfl

theorem logical_same_arm (p : List Bool) (rs : List V) (a b : Nat)
    {d e : Decoded} (hd : follow 59 Port.root [] (p ++ zeros a) = some d)
    (he : follow 59 Port.root [] (p ++ zeros b) = some e) :
    logicalDecoded rs d = logicalDecoded rs e := by
  suffices same : ∀ (a b : Nat) {d e : Decoded}, a ≤ b →
      follow 59 Port.root [] (p ++ zeros a) = some d →
      follow 59 Port.root [] (p ++ zeros b) = some e →
      logicalDecoded rs d = logicalDecoded rs e by
    by_cases hle : a ≤ b
    · exact same a b hle hd he
    · exact (same b a (by omega) he hd).symm
  intro a b d e hle h₁ h₂
  have split : (p ++ zeros a) ++ zeros (b - a) = p ++ zeros b := by
    rw [List.append_assoc, List.replicate_append_replicate, show a + (b - a) = b by omega]
  have hExtend := follow_append h₁ (zeros (b - a))
  rw [split, h₂] at hExtend
  rw [(Option.some.inj hExtend)]
  exact (logical_suffix rs d _).symm

end PalomarI3380.Engine
