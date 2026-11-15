module
public import Internal.Model
public import CKernel.Equality
@[expose] public section
/-! # The defined equality in a model

The backward-transport lemmas of `CKernel.Equality` need the gate's label (the
code of the hull relation) and an auxiliary label to differ from the labels
involved; in a model of arithmetic codes exceed their labels, so the relation's
code and its successor will do. -/
namespace ZF209.Internal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CKernel.Generic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma lt_mem_left (a b : V) : a < mem a b :=
  lt_of_le_of_lt (le_trans (le_cantor_left a b) (le_four_mul _)) (by simp [mem])

lemma lt_mem_right (a b : V) : b < mem a b :=
  lt_of_le_of_lt (le_trans (le_cantor_right a b) (le_four_mul _)) (by simp [mem])

/-- Both arguments of `cand` are bounded by it. -/
lemma left_le_cand (a b : V) : a ≤ cand a b :=
  le_trans (left_le_imp a (cneg b)) (left_le_imp _ 1)

lemma right_le_cand (a b : V) : b ≤ cand a b :=
  le_trans (left_le_imp b 1) (le_trans (right_le_imp a (cneg b)) (left_le_imp _ 1))

lemma relIn_gt (a b w : V) :
    a < (codes : Codes V).relIn a b w ∧ b < (codes : Codes V).relIn a b w ∧
      w < (codes : Codes V).relIn a b w := by
  have h₁ : mem w a ≤ (codes : Codes V).relIn a b w :=
    le_trans (left_le_imp _ 1) (left_le_cand _ _)
  have h₂ : mem b b ≤ (codes : Codes V).relIn a b w :=
    le_trans (left_le_imp _ _) (right_le_cand _ _)
  exact ⟨lt_of_lt_of_le (lt_mem_right w a) h₁, lt_of_lt_of_le (lt_mem_left b b) h₂,
    lt_of_lt_of_le (lt_mem_left w a) h₁⟩

lemma relOut_gt (a b w : V) :
    a < (codes : Codes V).relOut a b w ∧ b < (codes : Codes V).relOut a b w ∧
      w < (codes : Codes V).relOut a b w := by
  have h₁ : mem a w ≤ (codes : Codes V).relOut a b w :=
    le_trans (left_le_imp _ 1) (left_le_cand _ _)
  have h₂ : mem b b ≤ (codes : Codes V).relOut a b w :=
    le_trans (left_le_imp _ _) (right_le_cand _ _)
  exact ⟨lt_of_lt_of_le (lt_mem_left a w) h₁, lt_of_lt_of_le (lt_mem_left b b) h₂,
    lt_of_lt_of_le (lt_mem_right a w) h₁⟩

variable {D : 𝚺ᴬ₁.Semisentence 1}

/-- The calculus with the defined equality binding `z`. -/
noncomputable def ProvRules.eqLogic (h : ProvRules D V) (z : V) : EqLogic V :=
  h.sys.toEqLogic z
    (fun a b w hab haw _ => by
      obtain ⟨ha, hb, hw⟩ := relIn_gt (V := V) a b w
      exact h.sys.backIn a b w ((codes : Codes V).relIn a b w + 1) hab haw ha.ne' hb.ne' hw.ne'
        (ne_of_lt (lt_add_one _))
        (ne_of_gt (lt_trans ha (by simp))) (ne_of_gt (lt_trans hb (by simp)))
        (ne_of_gt (lt_trans hw (by simp))))
    (fun a b w hab haw _ => by
      obtain ⟨ha, hb, hw⟩ := relOut_gt (V := V) a b w
      exact h.sys.backOut a b w ((codes : Codes V).relOut a b w + 1) hab haw ha.ne' hb.ne' hw.ne'
        (ne_of_lt (lt_add_one _))
        (ne_of_gt (lt_trans ha (by simp))) (ne_of_gt (lt_trans hb (by simp)))
        (ne_of_gt (lt_trans hw (by simp))))

end ZF209.Internal
