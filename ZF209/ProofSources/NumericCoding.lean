module
public import SemanticBasics
@[expose] public section
namespace C209Soundness

def cantor (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

theorem triangular_ge (s : Nat) : s ≤ s * (s + 1) / 2 := by
  by_cases h : s = 0
  · subst s; simp
  · have hs : 2 ≤ s + 1 := by omega
    have hm := Nat.mul_le_mul_left s hs
    have hd := Nat.div_le_div_right hm (c := 2)
    have he : s * 2 / 2 = s := by omega
    omega

theorem cantor_ge_left (a b : Nat) : a ≤ cantor a b := by
  have h := triangular_ge (a + b)
  unfold cantor
  omega

theorem cantor_ge_right (a b : Nat) : b ≤ cantor a b := by
  unfold cantor
  omega

inductive Formula where
  | truth : Formula
  | imp : Formula → Formula → Formula
  | mem : Nat → Nat → Formula
  | all : Nat → Formula → Formula
  | eq : Nat → Nat → Formula

def Formula.code : Formula → Nat
  | .truth => 0
  | .imp p q => 4 * cantor p.code q.code
  | .mem i j => 4 * cantor i j + 1
  | .all i p => 4 * cantor p.code i + 2
  | .eq i j => 4 * cantor i j + 3

def Formula.LabelsLT : Formula → Nat → Prop
  | .truth, _ => True
  | .imp p q, n => p.LabelsLT n ∧ q.LabelsLT n
  | .mem i j, n => i < n ∧ j < n
  | .all i p, n => i < n ∧ p.LabelsLT n
  | .eq i j, n => i < n ∧ j < n

theorem Formula.labels_mono (p : Formula) {n m : Nat} (h : n ≤ m)
    (hp : p.LabelsLT n) : p.LabelsLT m := by
  induction p with
  | truth => trivial
  | imp p q ihp ihq => exact ⟨ihp hp.1, ihq hp.2⟩
  | mem i j => exact ⟨Nat.lt_of_lt_of_le hp.1 h, Nat.lt_of_lt_of_le hp.2 h⟩
  | all i p ih => exact ⟨Nat.lt_of_lt_of_le hp.1 h, ih hp.2⟩
  | eq i j => exact ⟨Nat.lt_of_lt_of_le hp.1 h, Nat.lt_of_lt_of_le hp.2 h⟩

theorem Formula.labels_below_code (p : Formula) : p.LabelsLT p.code := by
  induction p with
  | truth => trivial
  | imp p q ihp ihq =>
      have hp := cantor_ge_left p.code q.code
      have hq := cantor_ge_right p.code q.code
      exact ⟨p.labels_mono (by simp only [Formula.code]; omega) ihp,
        q.labels_mono (by simp only [Formula.code]; omega) ihq⟩
  | mem i j =>
      have hi := cantor_ge_left i j
      have hj := cantor_ge_right i j
      simp only [Formula.LabelsLT, Formula.code]
      omega
  | all i p ih =>
      have hi := cantor_ge_right p.code i
      have hp := cantor_ge_left p.code i
      exact ⟨by simp only [Formula.code]; omega,
        p.labels_mono (by simp only [Formula.code]; omega) ih⟩
  | eq i j =>
      have hi := cantor_ge_left i j
      have hj := cantor_ge_right i j
      simp only [Formula.LabelsLT, Formula.code]
      omega

def Formula.Fresh : Formula → Nat → Prop
  | .truth, _ => True
  | .imp p q, x => p.Fresh x ∧ q.Fresh x
  | .mem i j, x => i ≠ x ∧ j ≠ x
  | .all i p, x => i ≠ x ∧ p.Fresh x
  | .eq i j, x => i ≠ x ∧ j ≠ x

theorem Formula.labels_fresh (p : Formula) (x : Nat) (h : p.LabelsLT x) : p.Fresh x := by
  induction p with
  | truth => trivial
  | imp p q ihp ihq => exact ⟨ihp h.1, ihq h.2⟩
  | mem i j => exact ⟨Nat.ne_of_lt h.1, Nat.ne_of_lt h.2⟩
  | all i p ih => exact ⟨Nat.ne_of_lt h.1, ih h.2⟩
  | eq i j => exact ⟨Nat.ne_of_lt h.1, Nat.ne_of_lt h.2⟩

theorem Formula.self_fresh (p : Formula) : p.Fresh p.code :=
  p.labels_fresh p.code p.labels_below_code

universe u
variable {α : Type u}
def Formula.eval (mem : α → α → Prop) : Formula → Assignment α → Prop
  | .truth, _ => True
  | .imp p q, s => p.eval mem s → q.eval mem s
  | .mem i j, s => mem (s i) (s j)
  | .all i p, s => ∀ v, p.eval mem (update s i v)
  | .eq i j, s => s i = s j

theorem Formula.eval_fresh (p : Formula) (x : Nat) (hf : p.Fresh x)
    (mem : α → α → Prop) (s : Assignment α) (v : α) :
    p.eval mem (update s x v) ↔ p.eval mem s := by
  induction p generalizing s with
  | truth => exact Iff.rfl
  | imp p q ihp ihq =>
      simp only [Formula.eval]
      rw [ihp hf.1 s, ihq hf.2 s]
  | mem i j => simp only [Formula.eval, update, ite_eq_right hf.1, ite_eq_right hf.2]
  | eq i j => simp only [Formula.eval, update, ite_eq_right hf.1, ite_eq_right hf.2]
  | all i p ih =>
      constructor
      · intro h a
        have ha := h a
        rw [update_commute s x i (Ne.symm hf.1) v a] at ha
        exact (ih hf.2 (update s i a)).mp ha
      · intro h a
        change p.eval mem (update (update s x v) i a)
        rw [update_commute s x i (Ne.symm hf.1) v a]
        exact (ih hf.2 (update s i a)).mpr (h a)

theorem Formula.eval_self_independent (p : Formula) (mem : α → α → Prop)
    (s : Assignment α) (v : α) :
    p.eval mem (update s p.code v) ↔ p.eval mem s :=
  p.eval_fresh p.code p.self_fresh mem s v

end C209Soundness
