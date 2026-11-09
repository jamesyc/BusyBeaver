module

public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The PA211 statement

The arithmetic language has zero, one, addition, multiplication, order and
logical equality. PA is given by the discretely ordered arithmetic axioms
below and the full first-order induction schema with parameters.

The trace uses the arithmetic coding from Foundation revision
c3eb37ae896dc8f1d239ba1511e74d9f25e9d158 and the transition rows from
BusyBeaver's `Lean/data/pa211.tm`. The Solution proves that the trace claim
agrees with the existing exact sentence in all PA models.
-/

namespace PA211.Palomar

/-- An interpretation of the symbols of the language of arithmetic. -/
structure Arithmetic (M : Type) where
  zero : M
  one : M
  add : M → M → M
  mul : M → M → M
  lt : M → M → Prop

/-- Arithmetic terms with bound variables in `Fin n` and parameters in `ξ`. -/
inductive Term (ξ : Type) (n : Nat)
  | bound : Fin n → Term ξ n
  | param : ξ → Term ξ n
  | zero | one
  | add : Term ξ n → Term ξ n → Term ξ n
  | mul : Term ξ n → Term ξ n → Term ξ n

/-- First-order arithmetic in negation normal form. Index zero denotes the newest binder. -/
inductive Formula (ξ : Type) : Nat → Type
  | top : Formula ξ n
  | bot : Formula ξ n
  | eq : Term ξ n → Term ξ n → Formula ξ n
  | ne : Term ξ n → Term ξ n → Formula ξ n
  | lt : Term ξ n → Term ξ n → Formula ξ n
  | nlt : Term ξ n → Term ξ n → Formula ξ n
  | and : Formula ξ n → Formula ξ n → Formula ξ n
  | or : Formula ξ n → Formula ξ n → Formula ξ n
  | all : Formula ξ (n + 1) → Formula ξ n
  | ex : Formula ξ (n + 1) → Formula ξ n

abbrev Sentence := Formula Empty 0

def Term.eval (A : Arithmetic M) (b : Fin n → M) (f : ξ → M) : Term ξ n → M
  | .bound i => b i
  | .param x => f x
  | .zero => A.zero
  | .one => A.one
  | .add t u => A.add (t.eval A b f) (u.eval A b f)
  | .mul t u => A.mul (t.eval A b f) (u.eval A b f)

def Formula.eval (A : Arithmetic M) (f : ξ → M) :
    {n : Nat} → (Fin n → M) → Formula ξ n → Prop
  | _, _, .top => True
  | _, _, .bot => False
  | _, b, .eq t u => t.eval A b f = u.eval A b f
  | _, b, .ne t u => t.eval A b f ≠ u.eval A b f
  | _, b, .lt t u => A.lt (t.eval A b f) (u.eval A b f)
  | _, b, .nlt t u => ¬ A.lt (t.eval A b f) (u.eval A b f)
  | _, b, .and p q => p.eval A f b ∧ q.eval A f b
  | _, b, .or p q => p.eval A f b ∨ q.eval A f b
  | _, b, .all p => ∀ x, p.eval A f (Fin.cons x b)
  | _, b, .ex p => ∃ x, p.eval A f (Fin.cons x b)

/-- The base axioms and full induction schema of first-order PA.
Equality is interpreted as equality. -/
structure IsPA (A : Arithmetic M) : Prop where
  addZero : ∀ x, A.add x A.zero = x
  addAssoc : ∀ x y z, A.add (A.add x y) z = A.add x (A.add y z)
  addComm : ∀ x y, A.add x y = A.add y x
  addEqOfLt : ∀ x y, A.lt x y → ∃ z, A.lt z (A.add y A.one) ∧ A.add x z = y
  zeroLe : ∀ x, A.zero = x ∨ A.lt A.zero x
  zeroLtOne : A.lt A.zero A.one
  oneLeOfZeroLt : ∀ x, A.lt A.zero x → A.one = x ∨ A.lt A.one x
  addLtAdd : ∀ x y z, A.lt x y → A.lt (A.add x z) (A.add y z)
  mulZero : ∀ x, A.mul x A.zero = A.zero
  mulOne : ∀ x, A.mul x A.one = x
  mulAssoc : ∀ x y z, A.mul (A.mul x y) z = A.mul x (A.mul y z)
  mulComm : ∀ x y, A.mul x y = A.mul y x
  mulLtMul : ∀ x y z, A.lt x y ∧ A.lt A.zero z → A.lt (A.mul x z) (A.mul y z)
  distr : ∀ x y z, A.mul x (A.add y z) = A.add (A.mul x y) (A.mul x z)
  ltIrrefl : ∀ x, ¬ A.lt x x
  ltTrans : ∀ x y z, A.lt x y ∧ A.lt y z → A.lt x z
  ltTri : ∀ x y, A.lt x y ∨ x = y ∨ A.lt y x
  induction : ∀ (p : Formula Nat 1) (f : Nat → M),
    p.eval A f ![A.zero] →
    (∀ x, p.eval A f ![x] → p.eval A f ![A.add x A.one]) →
    ∀ x, p.eval A f ![x]

/-- First-order consequence in all models of PA. Soundness and completeness
identify this with provability from PA. -/
def PAProvable (p : (M : Type) → Arithmetic M → Prop) : Prop :=
  ∀ (M : Type) (A : Arithmetic M), IsPA A → p M A

/-- The literal PA211 table. The action contains the bit written, the
direction (true means right), and the next state. State 215 has no outgoing row. -/
def transition (q : Nat) (read : Bool) : Option (Bool × Bool × Nat) :=
  match q, read with
  | 0, false => some (true, true, 1)
  | 0, true => some (true, true, 64)
  | 1, false => some (true, true, 91)
  | 1, true => some (true, true, 1)
  | 2, false => some (false, false, 2)
  | 2, true => some (true, false, 3)
  | 3, false => some (false, false, 4)
  | 3, true => some (true, false, 3)
  | 4, false => some (false, false, 6)
  | 4, true => some (true, false, 3)
  | 5, false => some (true, true, 7)
  | 5, true => some (false, false, 5)
  | 6, false => some (false, false, 10)
  | 6, true => some (true, false, 3)
  | 7, false => some (false, true, 7)
  | 7, true => some (false, true, 11)
  | 8, false => some (false, true, 83)
  | 8, true => some (true, true, 186)
  | 9, false => some (false, true, 15)
  | 9, true => some (true, true, 14)
  | 10, false => some (false, false, 16)
  | 10, true => some (true, false, 3)
  | 11, false => some (false, false, 17)
  | 11, true => some (false, true, 11)
  | 12, false => some (false, false, 27)
  | 12, true => some (true, true, 19)
  | 13, false => some (false, true, 20)
  | 13, true => some (true, true, 21)
  | 14, false => some (false, false, 88)
  | 14, true => some (true, false, 32)
  | 15, false => some (false, false, 12)
  | 15, true => some (false, true, 23)
  | 16, false => some (false, false, 24)
  | 16, true => some (true, false, 3)
  | 17, false => some (true, false, 2)
  | 17, true => some (false, false, 2)
  | 18, false => some (false, true, 25)
  | 18, true => some (false, true, 33)
  | 19, false => some (false, true, 93)
  | 19, true => some (false, false, 104)
  | 20, false => some (false, true, 29)
  | 20, true => some (true, true, 30)
  | 21, false => some (false, true, 31)
  | 21, true => some (true, true, 32)
  | 22, false => some (false, true, 25)
  | 22, true => some (false, true, 60)
  | 23, false => some (false, true, 34)
  | 23, true => some (true, true, 23)
  | 24, false => some (false, false, 35)
  | 24, true => some (true, false, 3)
  | 25, false => some (false, false, 36)
  | 25, true => some (false, true, 1)
  | 26, false => some (false, true, 37)
  | 26, true => some (true, true, 26)
  | 27, false => some (false, true, 177)
  | 27, true => some (true, true, 38)
  | 28, false => some (false, true, 39)
  | 28, true => some (false, false, 40)
  | 29, false => some (false, true, 41)
  | 29, true => some (true, true, 42)
  | 30, false => some (false, true, 43)
  | 30, true => some (true, true, 44)
  | 31, false => some (false, true, 45)
  | 31, true => some (true, true, 46)
  | 32, false => some (false, true, 22)
  | 32, true => some (true, true, 47)
  | 33, false => some (false, true, 48)
  | 33, true => some (true, true, 33)
  | 34, false => some (false, true, 33)
  | 34, true => some (true, true, 34)
  | 35, false => some (false, false, 50)
  | 35, true => some (true, false, 3)
  | 36, false => some (true, true, 36)
  | 36, true => some (true, false, 2)
  | 37, false => some (false, true, 51)
  | 37, true => some (true, true, 37)
  | 38, false => some (false, true, 14)
  | 38, true => some (true, true, 53)
  | 39, false => some (false, false, 12)
  | 39, true => some (false, true, 37)
  | 40, false => some (false, false, 5)
  | 40, true => some (true, false, 54)
  | 41, false => some (false, true, 25)
  | 41, true => some (false, true, 26)
  | 42, false => some (false, true, 14)
  | 42, true => some (false, false, 17)
  | 43, false => some (false, true, 56)
  | 43, true => some (true, true, 57)
  | 44, false => some (false, true, 58)
  | 44, true => some (true, true, 59)
  | 45, false => some (false, true, 25)
  | 45, true => some (false, true, 55)
  | 46, false => some (false, true, 61)
  | 46, true => some (true, true, 62)
  | 47, false => some (false, true, 63)
  | 47, true => some (false, false, 17)
  | 48, false => some (false, true, 26)
  | 48, true => some (true, true, 48)
  | 49, false => some (false, false, 36)
  | 49, true => some (false, true, 64)
  | 50, false => some (false, false, 74)
  | 50, true => some (true, false, 3)
  | 51, false => some (false, true, 17)
  | 51, true => some (true, true, 51)
  | 52, false => some (false, true, 145)
  | 52, true => some (true, true, 141)
  | 53, false => some (false, true, 68)
  | 53, true => some (true, true, 69)
  | 54, false => some (false, false, 40)
  | 54, true => some (true, false, 54)
  | 55, false => some (false, true, 23)
  | 55, true => some (true, true, 55)
  | 56, false => some (false, false, 12)
  | 56, true => some (false, true, 51)
  | 57, false => some (false, true, 61)
  | 57, true => some (false, false, 17)
  | 58, false => some (false, true, 70)
  | 58, true => some (true, true, 71)
  | 59, false => some (false, true, 62)
  | 59, true => some (true, true, 72)
  | 60, false => some (false, true, 55)
  | 60, true => some (true, true, 60)
  | 61, false => some (false, true, 49)
  | 61, true => some (false, true, 26)
  | 62, false => some (false, false, 29)
  | 62, true => some (true, false, 73)
  | 63, false => some (false, false, 116)
  | 63, true => some (true, false, 31)
  | 64, false => some (false, true, 0)
  | 64, true => some (true, true, 64)
  | 65, false => some (false, true, 96)
  | 65, true => some (true, true, 147)
  | 66, false => some (true, true, 180)
  | 66, true => some (true, false, 54)
  | 67, false => some (false, true, 142)
  | 67, true => some (true, true, 143)
  | 68, false => some (false, true, 76)
  | 68, true => some (true, true, 215)
  | 69, false => some (false, false, 192)
  | 69, true => some (true, true, 32)
  | 70, false => some (false, true, 41)
  | 70, true => some (true, true, 63)
  | 71, false => some (false, false, 88)
  | 71, true => some (true, true, 77)
  | 72, false => some (false, true, 56)
  | 72, true => some (true, false, 78)
  | 73, false => some (false, true, 79)
  | 73, true => some (true, true, 80)
  | 74, false => some (false, true, 74)
  | 74, true => some (true, true, 81)
  | 75, false => some (false, false, 143)
  | 75, true => some (true, false, 139)
  | 76, false => some (false, true, 84)
  | 76, true => some (true, true, 85)
  | 77, false => some (false, true, 88)
  | 77, true => some (true, false, 131)
  | 78, false => some (false, false, 107)
  | 78, true => some (true, true, 57)
  | 79, false => some (false, true, 49)
  | 79, true => some (false, true, 34)
  | 80, false => some (false, true, 90)
  | 80, true => some (false, false, 42)
  | 81, false => some (false, true, 173)
  | 81, true => some (true, true, 211)
  | 82, false => some (false, true, 95)
  | 82, true => some (true, true, 13)
  | 83, false => some (false, true, 87)
  | 83, true => some (true, true, 96)
  | 84, false => some (false, true, 202)
  | 84, true => some (true, true, 22)
  | 85, false => some (false, true, 115)
  | 85, true => some (true, true, 99)
  | 86, false => some (false, true, 147)
  | 86, true => some (true, true, 112)
  | 87, false => some (false, true, 101)
  | 87, true => some (true, true, 102)
  | 88, false => some (false, true, 79)
  | 88, true => some (true, true, 78)
  | 89, false => some (false, true, 100)
  | 89, true => some (true, true, 170)
  | 90, false => some (false, true, 104)
  | 90, true => some (true, true, 105)
  | 91, false => some (false, true, 66)
  | 91, true => some (false, true, 1)
  | 92, false => some (false, true, 28)
  | 92, true => some (true, true, 106)
  | 93, false => some (false, true, 98)
  | 93, true => some (true, true, 97)
  | 94, false => some (true, false, 109)
  | 94, true => some (true, false, 94)
  | 95, false => some (false, true, 20)
  | 95, true => some (true, true, 110)
  | 96, false => some (false, true, 61)
  | 96, true => some (true, true, 61)
  | 97, false => some (false, true, 163)
  | 97, true => some (true, true, 153)
  | 98, false => some (false, false, 27)
  | 98, true => some (true, true, 111)
  | 99, false => some (false, true, 104)
  | 99, true => some (false, false, 203)
  | 100, false => some (false, true, 116)
  | 100, true => some (true, true, 117)
  | 101, false => some (false, true, 72)
  | 101, true => some (true, true, 59)
  | 102, false => some (false, true, 58)
  | 102, true => some (true, true, 118)
  | 103, false => some (false, true, 22)
  | 103, true => some (true, true, 119)
  | 104, false => some (false, true, 22)
  | 104, true => some (false, false, 11)
  | 105, false => some (false, true, 62)
  | 105, true => some (true, true, 42)
  | 106, false => some (false, true, 120)
  | 106, true => some (true, true, 9)
  | 107, false => some (false, true, 100)
  | 107, true => some (true, true, 121)
  | 108, false => some (false, true, 87)
  | 108, true => some (true, true, 169)
  | 109, false => some (false, false, 203)
  | 109, true => some (false, false, 94)
  | 110, false => some (false, true, 123)
  | 110, true => some (true, true, 103)
  | 111, false => some (false, true, 75)
  | 111, true => some (true, true, 114)
  | 112, false => some (false, true, 108)
  | 112, true => some (true, true, 177)
  | 113, false => some (false, true, 146)
  | 113, true => some (true, true, 144)
  | 114, false => some (false, true, 137)
  | 114, true => some (true, true, 134)
  | 115, false => some (false, false, 130)
  | 115, true => some (false, false, 2)
  | 116, false => some (false, true, 39)
  | 116, true => some (true, true, 73)
  | 117, false => some (false, true, 62)
  | 117, true => some (true, true, 131)
  | 118, false => some (false, true, 62)
  | 118, true => some (true, true, 132)
  | 119, false => some (false, true, 71)
  | 119, true => some (false, false, 17)
  | 120, false => some (false, true, 15)
  | 120, true => some (true, true, 131)
  | 121, false => some (false, true, 22)
  | 121, true => some (true, true, 133)
  | 123, false => some (false, true, 135)
  | 123, true => some (true, false, 21)
  | 124, false => some (false, true, 129)
  | 124, true => some (true, true, 176)
  | 125, false => some (false, true, 200)
  | 125, true => some (true, true, 167)
  | 126, false => some (false, true, 75)
  | 126, true => some (true, true, 172)
  | 127, false => some (false, true, 128)
  | 127, true => some (false, false, 203)
  | 128, false => some (false, true, 125)
  | 128, true => some (true, true, 136)
  | 129, false => some (false, true, 13)
  | 129, true => some (true, true, 139)
  | 130, false => some (false, true, 31)
  | 130, true => some (true, true, 70)
  | 131, false => some (false, true, 39)
  | 131, true => some (true, false, 123)
  | 132, false => some (false, true, 175)
  | 132, true => some (false, false, 17)
  | 133, false => some (false, true, 151)
  | 133, true => some (false, false, 17)
  | 134, false => some (false, true, 148)
  | 134, true => some (true, true, 127)
  | 135, false => some (false, true, 25)
  | 135, true => some (false, true, 48)
  | 136, false => some (false, true, 146)
  | 136, true => some (true, true, 152)
  | 137, false => some (false, true, 157)
  | 137, true => some (true, true, 156)
  | 138, false => some (false, true, 95)
  | 138, true => some (true, true, 155)
  | 139, false => some (false, true, 171)
  | 139, true => some (true, true, 162)
  | 140, false => some (false, true, 13)
  | 140, true => some (true, true, 155)
  | 141, false => some (false, true, 87)
  | 141, true => some (true, false, 162)
  | 142, false => some (false, true, 87)
  | 142, true => some (true, true, 154)
  | 143, false => some (false, false, 149)
  | 143, true => some (true, false, 159)
  | 144, false => some (false, true, 83)
  | 144, true => some (true, true, 87)
  | 145, false => some (false, true, 155)
  | 145, true => some (true, true, 13)
  | 146, false => some (false, true, 82)
  | 146, true => some (true, true, 141)
  | 147, false => some (false, false, 67)
  | 147, true => some (true, false, 139)
  | 148, false => some (false, true, 188)
  | 148, true => some (true, true, 165)
  | 149, false => some (false, true, 155)
  | 149, true => some (true, true, 113)
  | 151, false => some (false, true, 49)
  | 151, true => some (false, true, 33)
  | 152, false => some (false, true, 174)
  | 152, true => some (true, true, 182)
  | 153, false => some (false, false, 206)
  | 153, true => some (true, true, 95)
  | 154, false => some (false, true, 164)
  | 154, true => some (true, true, 175)
  | 155, false => some (false, true, 20)
  | 155, true => some (true, true, 166)
  | 156, false => some (false, true, 191)
  | 156, true => some (true, true, 183)
  | 157, false => some (false, true, 155)
  | 157, true => some (true, true, 95)
  | 158, false => some (false, true, 124)
  | 158, true => some (true, true, 160)
  | 159, false => some (false, true, 96)
  | 159, true => some (true, true, 158)
  | 160, false => some (false, false, 8)
  | 160, true => some (true, true, 140)
  | 161, false => some (false, true, 147)
  | 161, true => some (true, true, 169)
  | 162, false => some (false, true, 144)
  | 162, true => some (true, true, 168)
  | 163, false => some (false, true, 192)
  | 163, true => some (true, true, 29)
  | 164, false => some (false, true, 157)
  | 164, true => some (true, true, 141)
  | 165, false => some (false, true, 67)
  | 165, true => some (true, true, 144)
  | 166, false => some (false, true, 177)
  | 166, true => some (true, true, 121)
  | 167, false => some (false, true, 143)
  | 167, true => some (true, true, 161)
  | 168, false => some (false, true, 75)
  | 168, true => some (true, true, 61)
  | 169, false => some (false, true, 143)
  | 169, true => some (true, true, 87)
  | 170, false => some (false, true, 103)
  | 170, true => some (true, true, 95)
  | 171, false => some (false, true, 138)
  | 171, true => some (true, true, 83)
  | 172, false => some (false, true, 171)
  | 172, true => some (true, true, 75)
  | 173, false => some (false, true, 92)
  | 173, true => some (true, true, 107)
  | 174, false => some (false, true, 149)
  | 174, true => some (true, true, 184)
  | 175, false => some (false, true, 96)
  | 175, true => some (true, false, 209)
  | 176, false => some (false, true, 164)
  | 176, true => some (true, true, 52)
  | 177, false => some (false, true, 18)
  | 177, true => some (true, false, 130)
  | 178, false => some (false, true, 76)
  | 178, true => some (true, true, 115)
  | 179, false => some (false, true, 105)
  | 179, true => some (true, true, 123)
  | 180, false => some (false, false, 40)
  | 180, true => some (true, false, 109)
  | 181, false => some (false, true, 167)
  | 181, true => some (true, true, 155)
  | 182, false => some (false, true, 185)
  | 182, true => some (true, true, 190)
  | 183, false => some (false, true, 138)
  | 183, true => some (true, true, 194)
  | 184, false => some (false, true, 195)
  | 184, true => some (true, true, 196)
  | 185, false => some (false, true, 197)
  | 185, true => some (true, true, 198)
  | 186, false => some (false, true, 153)
  | 186, true => some (true, true, 187)
  | 187, false => some (false, true, 171)
  | 187, true => some (true, true, 181)
  | 188, false => some (false, true, 65)
  | 188, true => some (true, true, 8)
  | 189, false => some (false, true, 147)
  | 189, true => some (true, true, 126)
  | 190, false => some (false, true, 86)
  | 190, true => some (true, true, 199)
  | 191, false => some (false, true, 69)
  | 191, true => some (true, true, 201)
  | 192, false => some (false, true, 89)
  | 192, true => some (true, true, 87)
  | 193, false => some (false, true, 29)
  | 193, true => some (true, true, 213)
  | 194, false => some (false, true, 160)
  | 194, true => some (true, true, 204)
  | 195, false => some (false, true, 145)
  | 195, true => some (true, true, 146)
  | 196, false => some (false, true, 210)
  | 196, true => some (true, true, 207)
  | 197, false => some (false, true, 155)
  | 197, true => some (true, true, 208)
  | 198, false => some (false, true, 209)
  | 198, true => some (true, true, 108)
  | 199, false => some (false, true, 178)
  | 199, true => some (true, true, 212)
  | 200, false => some (false, true, 159)
  | 200, true => some (true, true, 189)
  | 201, false => some (false, true, 87)
  | 201, true => some (true, true, 192)
  | 202, false => some (false, true, 45)
  | 202, true => some (true, true, 99)
  | 203, false => some (false, false, 5)
  | 203, true => some (false, false, 203)
  | 204, false => some (false, true, 141)
  | 204, true => some (true, true, 142)
  | 206, false => some (false, true, 207)
  | 206, true => some (true, true, 178)
  | 207, false => some (false, true, 141)
  | 207, true => some (true, true, 52)
  | 208, false => some (false, true, 108)
  | 208, true => some (true, true, 108)
  | 209, false => some (false, true, 83)
  | 209, true => some (true, true, 210)
  | 210, false => some (false, true, 155)
  | 210, true => some (true, true, 52)
  | 211, false => some (false, true, 12)
  | 211, true => some (true, true, 193)
  | 212, false => some (false, true, 179)
  | 212, true => some (true, true, 178)
  | 213, false => some (false, true, 21)
  | 213, true => some (true, true, 38)
  | _, _ => none

/-- The labels of the working states, in increasing order. -/
def workingStates : List Nat :=
  (List.range 215).filter (fun q => (transition q false).isSome)

/-- Each row gives the state and bit read, followed by the transition action. -/
def rows : List (Nat × Bool × Bool × Bool × Nat) :=
  (List.range 215).flatMap fun q => [false, true].filterMap fun b =>
    (transition q b).map fun (w, d, t) => (q, b, w, d, t)

/-- The left side is read away from the head. The right side starts at the head.
Missing cells are zero. -/
structure Configuration where
  state : Nat
  left : List Bool
  right : List Bool

def trim : List Bool → List Bool
  | [] => []
  | b :: tail => if b = false ∧ trim tail = [] then [] else b :: trim tail

def config (q : Nat) (l r : List Bool) : Configuration :=
  ⟨q, trim l, trim r⟩

def step (c : Configuration) : Option Configuration :=
  match transition c.state (c.right.headD false) with
  | none => none
  | some (w, true, q) => some (config q (w :: c.left) c.right.tail)
  | some (w, false, q) => some (config q c.left.tail (c.left.headD false :: w :: c.right.tail))

def run : Nat → Configuration → Option Configuration
  | 0, c => some c
  | n + 1, c => (step c).bind (run n)

/-- The machine reaches a configuration with no transition from state 0 on the blank tape. -/
def Halts : Prop :=
  ∃ n c, run n (config 0 [] []) = some c ∧ step c = none

/- The arithmetic of the trace uses the same model, including in nonstandard models. -/
section Coding
variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M]

local infix:50 " ≼ " => fun a b => ¬ b < a

def numeral : Nat → M
  | 0 => 0
  | 1 => 1
  | n + 2 => numeral (n + 1) + 1

def square (a : M) : M := a * a

def divides (a b : M) : Prop := ∃ c, c ≼ b ∧ b = a * c

def quotient (q a b : M) : Prop :=
  (0 < b → b * q ≼ a ∧ a < b * (q + 1)) ∧ (b = 0 → q = 0)

def difference (r a b : M) : Prop :=
  (b ≼ a → a = b + r) ∧ (a < b → r = 0)

def remainder (r a b : M) : Prop :=
  ∃ q, q ≼ a ∧ quotient q a b ∧ difference r a (b * q)

def digit (r b a : M) : Prop := ∃ q, q ≼ a ∧ quotient q a b ∧ remainder r q b

/-- A number with no odd divisor greater than one is a power of two. -/
def powerOfTwo (a : M) : Prop :=
  0 < a ∧ ∀ d, d ≼ a → 1 < d → divides d a → divides (1 + 1) d

/-- The bit of `a` at the place value `p`, where `p` is a power of two. -/
def bitAt (p a : M) : Prop := ∃ q, q ≼ a ∧ quotient q a p ∧ ¬ divides (1 + 1) q

def squareRoot (r a : M) : Prop := square r ≼ a ∧ a < square (r + 1)

/-- The set of places in this bit mask starts at 2 and is closed under squaring
up to its bound. It identifies the place values 2, 4, 16, 256, and so on. -/
def squaringMask (m : M) : Prop :=
  ¬ bitAt 1 m ∧ bitAt (1 + 1) m ∧
    ∀ p, p ≼ m → powerOfTwo p → 1 + 1 < p →
      (bitAt p m ↔ ∃ r, r ≼ p ∧ squareRoot r p ∧ square r = p ∧ bitAt r m)

def digitPlace (p : M) : Prop :=
  powerOfTwo p ∧ ∃ m < (1 + 1) * p, squaringMask m ∧ bitAt p m

/-- First-order graph of `y = 2^x`. The digit streams record the binary
recurrence `(x, y) ↦ (2*x, y*y)` or `(2*x+1, 2*y*y)`.
This is the exponentiation coding used by Foundation. -/
def twoTo (x y : M) : Prop :=
  (x = 0 ∧ y = 1) ∨
    ∃ xs, xs ≼ square y * y * y ∧ ∃ ys, ys ≼ square y * y * y ∧
      (digit 1 (numeral 4) xs ∧ digit (1 + 1) (numeral 4) ys) ∧
      (∀ p, p ≼ y → p ≠ 1 + 1 → digitPlace p →
        ((∃ a, a ≼ xs ∧ digit a p xs ∧ digit ((1 + 1) * a) (square p) xs) ∧
          (∃ b, b ≼ ys ∧ digit b p ys ∧ digit (square b) (square p) ys)) ∨
        ((∃ a, a ≼ xs ∧ digit a p xs ∧ digit ((1 + 1) * a + 1) (square p) xs) ∧
          (∃ b, b ≼ ys ∧ digit b p ys ∧ digit ((1 + 1) * square b) (square p) ys))) ∧
      ∃ p, p ≼ square y ∧ p ≠ 1 + 1 ∧ digitPlace p ∧ digit x p xs ∧ digit y p ys

/-- Membership in the finite set encoded by the binary expansion of `s`. -/
def contains (i s : M) : Prop := ∃ p, p ≼ s ∧ twoTo i p ∧ bitAt p s

/-- The pairing function sends `(a,b)` to `b²+a` if `a<b`, and `a²+a+b` otherwise. -/
def pairCode (c a b : M) : Prop :=
  (a < b ∧ c = square b + a) ∨ (b ≼ a ∧ c = square a + a + b)

def tripleCode (c a b d : M) : Prop := ∃ bd, pairCode bd b d ∧ pairCode c a bd

/-- A positive list code is one plus the pair of the head and tail.
Both projections of the empty code are zero. -/
def unconsCode (v a b : M) : Prop :=
  (v = 0 ∧ a = 0 ∧ b = 0) ∨ ∃ p, v = p + 1 ∧ pairCode p a b

/-- The value at index `i` of the nested-pair list code `v`.
A binary set certifies the tail computations. Every triple in the set
either gives the head at index zero or has a predecessor in the set. -/
def nthCode (v i x : M) : Prop :=
  ∃ s c, tripleCode c v i x ∧ contains c s ∧
    ∀ d, contains d s →
      (∃ w z t, unconsCode w z t ∧ tripleCode d w 0 z) ∨
      (∃ w j z a t e, tripleCode d w (j + 1) z ∧ unconsCode w a t ∧
        tripleCode e t j z ∧ contains e s)

/-- One transition written in arithmetic. The tape halves are base-two
numerals, with the nearest cell in the low bit. -/
def rowCode (row : Nat × Bool × Bool × Bool × Nat) (q l r q' l' r' : M) : Prop :=
  let (src, read, write, right, dst) := row
  q = numeral src ∧ q' = numeral dst ∧
    if right then
      ∃ t, r = (1 + 1) * t + numeral read.toNat ∧
        l' = (1 + 1) * l + numeral write.toNat ∧ r' = t
    else
      ∃ t u e, (e = 0 ∨ e = 1) ∧ l = (1 + 1) * u + e ∧
        r = (1 + 1) * t + numeral read.toNat ∧ l' = u ∧
        r' = (1 + 1) * ((1 + 1) * t + numeral write.toNat) + e

/-- The disjunction over the 422 literal arithmetic transition rows. -/
def stepCode (q l r q' l' r' : M) : Prop :=
  ∃ row ∈ rows, rowCode row q l r q' l' r'

/-- The states and tape halves along the computation are coded by three lists.
The length, indices and list codes range over the model of arithmetic. -/
def traceCode : Prop :=
  ∃ n qs ls rs : M, nthCode qs 0 0 ∧ nthCode ls 0 0 ∧ nthCode rs 0 0 ∧
    nthCode qs n (numeral 215) ∧
    ∀ i < n, ∃ q l r q' l' r',
      nthCode qs i q ∧ nthCode ls i l ∧ nthCode rs i r ∧
      nthCode qs (i + 1) q' ∧ nthCode ls (i + 1) l' ∧ nthCode rs (i + 1) r' ∧
      stepCode q l r q' l' r'

end Coding

/-- The first-order trace claim, given by its interpretation in an arithmetic model. -/
def haltingSentence (M : Type) (A : Arithmetic M) : Prop :=
  letI : Zero M := ⟨A.zero⟩
  letI : One M := ⟨A.one⟩
  letI : Add M := ⟨A.add⟩
  letI : Mul M := ⟨A.mul⟩
  letI : LT M := ⟨A.lt⟩
  traceCode (M := M)

/-- The exact arithmetic nonhalting claim. -/
def nonhaltingSentence (M : Type) (A : Arithmetic M) : Prop :=
  ¬ haltingSentence M A


end PA211.Palomar
