module
public import I3_334Support.Equations
@[expose] public section

namespace PalomarI3380

namespace Cantor

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

theorem triangle_twice (n : Nat) : 2 * triangle n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Nat.mul_add] at ih
      simp only [triangle, Nat.mul_add, Nat.succ_mul, Nat.mul_succ]
      omega

theorem triangle_monotone {a b : Nat} (h : a ≤ b) : triangle a ≤ triangle b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_right ..)

def pair (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

theorem pair_as_triangle (a b : Nat) : pair a b = triangle (a + b) + b := by
  unfold pair
  rw [← triangle_twice, Nat.mul_comm 2, Nat.mul_div_cancel _ (by decide : 0 < 2)]

theorem right_le (a b : Nat) : b ≤ pair a b := by
  rw [pair_as_triangle]
  exact Nat.le_add_left ..

theorem positive_left {a : Nat} (h : 0 < a) (b : Nat) : 0 < pair a b := by
  have h₁ : triangle 1 ≤ triangle (a + b) := triangle_monotone (by omega)
  change 1 ≤ triangle (a + b) at h₁
  rw [pair_as_triangle]
  omega

private theorem lt_next (a b : Nat) : pair a b < triangle (a + b + 1) := by
  simp only [pair_as_triangle, triangle]
  omega

theorem pair_eq {a b x y : Nat} (h : pair a b = pair x y) : a = x ∧ b = y := by
  have noSmaller {a b x y : Nat} (h : pair a b = pair x y) : ¬ a + b < x + y := by
    intro hab
    have h₁ := Nat.lt_of_lt_of_le (lt_next a b) (triangle_monotone hab)
    have h₂ : triangle (x + y) ≤ pair x y := by
      rw [pair_as_triangle]
      exact Nat.le_add_right ..
    omega
  have sums : a + b = x + y := by
    have := noSmaller h
    have := noSmaller h.symm
    omega
  rw [pair_as_triangle, pair_as_triangle, sums] at h
  omega

theorem pair_surjective (n : Nat) : ∃ a b, pair a b = n := by
  induction n with
  | zero => exact ⟨0, 0, rfl⟩
  | succ n ih =>
      obtain ⟨a, b, rfl⟩ := ih
      cases a with
      | zero =>
          refine ⟨b + 1, 0, ?_⟩
          simp only [pair_as_triangle, Nat.add_zero, Nat.zero_add, triangle]
          omega
      | succ a =>
          refine ⟨a, b + 1, ?_⟩
          simp only [pair_as_triangle]
          rw [show a + (b + 1) = a + 1 + b by omega]
          omega

end Cantor

structure Token where
  arity : Nat
  tag : Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def Constant.tag : Constant → Nat
  | .J => 0
  | .D => 1
  | .T => 2  -- Unused by the literal manifest.
  | .S => 3  -- Unused by the literal manifest.
  | .U => 4
  | .E => 5
  | .I => 6

/-- Emit the prefix word, using an independent term word for each variable. -/
def Term.emit {V : Type} (variableWord : V → List Token) :
    Term V → List Token → List Token
  | .var x, tail => variableWord x ++ tail
  | .const c, tail => ⟨0, c.tag⟩ :: tail
  | .neg x, tail => ⟨1, 0⟩ :: x.emit variableWord tail
  | .choice x, tail => ⟨1, 1⟩ :: x.emit variableWord tail
  | .localRel x, tail => ⟨1, 2⟩ :: x.emit variableWord tail
  | .converse x, tail => ⟨1, 3⟩ :: x.emit variableWord tail
  | .nand x y, tail => ⟨2, 0⟩ :: x.emit variableWord (y.emit variableWord tail)
  | .product x y, tail => ⟨2, 1⟩ :: x.emit variableWord (y.emit variableWord tail)
  | .node x y z, tail =>
      ⟨3, 0⟩ :: x.emit variableWord (y.emit variableWord (z.emit variableWord tail))

theorem Term.emit_append {V : Type} (t : Term V) (v : V → List Token)
    (base tail : List Token) : t.emit v (base ++ tail) = t.emit v base ++ tail := by
  induction t generalizing base tail <;>
    simp only [Term.emit, List.append_assoc, List.cons_append, *]

theorem Term.emit_subst {V W : Type} (t : Term V) (σ : V → Term W)
    (v : W → List Token) (tail : List Token) :
    (t.subst σ).emit v tail = t.emit (fun x => (σ x).emit v []) tail := by
  induction t generalizing tail <;> simp only [Term.subst, Term.emit, *]
  case var x => exact (σ x).emit_append v [] tail

/-- The release's positive-arity encoding. The empty stream is zero;
every token, including a tag-zero constant, has positive leading arity. -/
def wordCode : List Token → Nat
  | [] => 0
  | token :: rest => Cantor.pair (token.arity + 1) (Cantor.pair token.tag (wordCode rest))

theorem wordCode_nonzero (t : Token) (rest : List Token) :
    0 < wordCode (t :: rest) := Cantor.positive_left (by omega) _

theorem wordCode_injective {a b : List Token} (h : wordCode a = wordCode b) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons t rest =>
          have := wordCode_nonzero t rest
          change 0 = wordCode (t :: rest) at h
          omega
  | cons t rest ih =>
      cases b with
      | nil =>
          have := wordCode_nonzero t rest
          change wordCode (t :: rest) = 0 at h
          omega
      | cons u tail =>
          rw [wordCode, wordCode] at h
          obtain ⟨arity, fields⟩ := Cantor.pair_eq h
          obtain ⟨tag, codes⟩ := Cantor.pair_eq fields
          have : t = u := by
            cases t
            cases u
            simp only at arity tag
            congr <;> omega
          rw [this, ih codes]

theorem code_D : wordCode ((Term.const .D : Term Empty).emit Empty.elim []) = 4 := rfl
theorem code_J : wordCode ((Term.const .J : Term Empty).emit Empty.elim []) = 1 := rfl

theorem accepting_word {ts : List Token} : wordCode ts = 1 ↔ ts = [⟨0, 0⟩] := by
  constructor
  · intro h
    exact wordCode_injective (h.trans code_J.symm)
  · rintro rfl
    exact code_J

end PalomarI3380
