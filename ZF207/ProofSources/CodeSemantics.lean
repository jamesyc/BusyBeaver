module
public import ComputableDecoding
public import CantorUniqueness
@[expose] public section
namespace C207Soundness
universe u
variable {α : Type u}

theorem Formula.code_zero_true (p : Formula) (hz : p.code = 0)
    (mem : α → α → Prop) (s : Assignment α) : p.eval mem s := by
  induction p with
  | truth => trivial
  | imp p q ihp ihq =>
      have hq := cantor_ge_right p.code q.code
      have hq0 : q.code = 0 := by simp only [Formula.code] at hz; omega
      intro _
      exact ihq hq0
  | mem i j => simp only [Formula.code] at hz; omega
  | all i p ih => simp only [Formula.code] at hz; omega
  | eq i j => simp only [Formula.code] at hz; omega

theorem Formula.code_eval_unique (n : Nat) :
    ∀ p q : Formula, p.code = n → q.code = n →
      ∀ (mem : α → α → Prop) (s : Assignment α), p.eval mem s ↔ q.eval mem s := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro p q hp hq mem s
      by_cases hz : n = 0
      · exact ⟨fun _ => q.code_zero_true (hq.trans hz) mem s, fun _ => p.code_zero_true (hp.trans hz) mem s⟩
      · cases p <;> cases q <;> simp only [Formula.code] at hp hq
        all_goals try omega
        case imp.imp a b c d =>
          have habc : cantor a.code b.code = cantor c.code d.code := by omega
          obtain ⟨hac, hbd⟩ := cantor_injective habc
          have ha : a.code < n := by have h := cantor_ge_left a.code b.code; omega
          have hb : b.code < n := by have h := cantor_ge_right a.code b.code; omega
          simp only [Formula.eval]
          rw [ih a.code ha a c rfl hac.symm mem s, ih b.code hb b d rfl hbd.symm mem s]
        case mem.mem a b c d =>
          have habc : cantor a b = cantor c d := by omega
          obtain ⟨ha, hb⟩ := cantor_injective habc
          subst c; subst d
          exact Iff.rfl
        case all.all i a j b =>
          have habc : cantor a.code i = cantor b.code j := by omega
          obtain ⟨hab, hij⟩ := cantor_injective habc
          subst j
          have ha : a.code < n := by have h := cantor_ge_left a.code i; omega
          constructor
          · intro h v
            exact (ih a.code ha a b rfl hab.symm mem (update s i v)).mp (h v)
          · intro h v
            exact (ih a.code ha a b rfl hab.symm mem (update s i v)).mpr (h v)
        case eq.eq a b c d =>
          have habc : cantor a b = cantor c d := by omega
          obtain ⟨ha, hb⟩ := cantor_injective habc
          subst c; subst d
          exact Iff.rfl

def decode (n : Nat) : Formula := decodeNat n
theorem decode_code (n : Nat) : (decode n).code = n := decodeNat_code n
def evalCode (mem : α → α → Prop) (n : Nat) (s : Assignment α) : Prop :=
  (decode n).eval mem s

theorem evalCode_of_formula (p : Formula) (mem : α → α → Prop) (s : Assignment α) :
    evalCode mem p.code s ↔ p.eval mem s :=
  Formula.code_eval_unique p.code (decode p.code) p (decode_code p.code) rfl mem s

theorem evalCode_self_independent (n : Nat) (mem : α → α → Prop)
    (s : Assignment α) (v : α) : evalCode mem n (update s n v) ↔ evalCode mem n s := by
  unfold evalCode
  have h := (decode n).eval_self_independent mem s v
  rw [decode_code] at h
  exact h

end C207Soundness
