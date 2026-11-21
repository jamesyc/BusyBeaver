module
public import I3_380.Search.Arithmetic.SourceCantor
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.SourceWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open SourceCantor

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- One token cell of the released source. Arity is stored one higher
so every token is represented by a positive word. -/
noncomputable def cons (arity tag rest : M) : M :=
  pairValue (arity+1) (pairValue tag rest)

noncomputable def arity (code : M) : M := decodeLeft code-1

noncomputable def tag (code : M) : M := decodeLeft (decodeRight code)

noncomputable def tail (code : M) : M := decodeRight (decodeRight code)

@[simp] theorem decodeLeft_cons (a t w : M) : decodeLeft (cons a t w) = a+1 :=
  (decode_pairValue _ _).1

@[simp] theorem decodeRight_cons (a t w : M) : decodeRight (cons a t w) = pairValue t w :=
  (decode_pairValue _ _).2

@[simp] theorem arity_cons (a t w : M) : arity (cons a t w) = a := by
  unfold arity cons
  rw [(decode_pairValue _ _).1]
  simp

@[simp] theorem tag_cons (a t w : M) : tag (cons a t w) = t := by
  unfold tag cons
  rw [(decode_pairValue _ _).2,(decode_pairValue t w).1]

@[simp] theorem tail_cons (a t w : M) : tail (cons a t w) = w := by
  unfold tail cons
  rw [(decode_pairValue _ _).2,(decode_pairValue t w).2]

theorem right_lt_pair {a : M} (positive : 0 < a) (b : M) : b < pairValue a b := by
  have sumPositive : 0 < a+b := lt_of_lt_of_le positive (by simp)
  have trianglePositive := lt_of_lt_of_le sumPositive (triangle_ge (a+b))
  unfold pairValue
  simpa only [add_zero,add_comm] using add_lt_add_right trianglePositive b

theorem tail_lt_cons (a t w : M) : w < cons a t w :=
  lt_of_le_of_lt (pairValue_bounds t w).2 (right_lt_pair (by simp) _)

theorem cons_positive (a t w : M) : 0 < cons a t w :=
  lt_of_le_of_lt (by simp) (tail_lt_cons a t w)

theorem positive_arity_uncons {w : M} (pos : 0 < decodeLeft w) :
    cons (arity w) (tag w) (tail w) = w := by
  unfold cons arity tag tail
  rw [tsub_add_cancel_of_le (pos_iff_one_le.mp pos),pairValue_decode,pairValue_decode]

theorem cons_standard (a t w : Nat) :
    cons a t w = Cantor.pair (a+1) (Cantor.pair t w) := by
  simp only [cons,SourceCantor.pair_standard]

@[definability] theorem cons_definable : 𝚺ᴬ₁-Function₃ (cons (M := M)) := by
  unfold cons
  definability

@[definability] theorem arity_definable : 𝚺ᴬ₁-Function₁ (arity (M := M)) := by
  unfold arity
  definability

@[definability] theorem tag_definable : 𝚺ᴬ₁-Function₁ (tag (M := M)) := by
  unfold tag
  definability

@[definability] theorem tail_definable : 𝚺ᴬ₁-Function₁ (tail (M := M)) := by
  unfold tail
  definability

end PalomarI3380.ArithmeticMachine.SourceWords
