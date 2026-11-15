module
public import SourceTrace
public import CantorUniqueness
@[expose] public section
namespace ZFR
open C209Soundness

def sourceNode (t a b : Nat) := 8 * cantor a b + t

theorem sourceNode_inj {t u a b c d : Nat} (ht : t < 8) (hu : u < 8) :
 sourceNode t a b = sourceNode u c d ↔ t = u ∧ a = c ∧ b = d := by
 constructor
 · intro h
   unfold sourceNode at h
   have htu : t = u := by omega
   have hp : cantor a b = cantor c d := by omega
   exact ⟨htu, cantor_injective hp⟩
 · rintro ⟨rfl,rfl,rfl⟩; rfl

theorem sourceNode_tag {t : Nat} (ht : t < 8) (a b : Nat) :
 sourceNode t a b % 8 = t := by unfold sourceNode; omega

theorem sourceNode_payload {t : Nat} (ht : t < 8) (a b : Nat) :
 sourceNode t a b / 8 = cantor a b := by unfold sourceNode; omega

def encodeFormula : Formula → Nat
 | .bot => 0
 | .mem a b => sourceNode 1 a b
 | .eq a b => sourceNode 2 a b
 | .and a b => sourceNode 3 (encodeFormula a) (encodeFormula b)
 | .or a b => sourceNode 4 (encodeFormula a) (encodeFormula b)
 | .imp a b => sourceNode 5 (encodeFormula a) (encodeFormula b)
 | .all a => sourceNode 6 (encodeFormula a) 0
 | .ex a => sourceNode 7 (encodeFormula a) 0

theorem sourceNode_ne_zero {t a b : Nat} (ht : 0 < t) : sourceNode t a b ≠ 0 := by
 unfold sourceNode; omega

theorem encodeFormula_injective : Function.Injective encodeFormula := by
 intro a
 induction a <;> intro b h <;> cases b <;>
 simp only [encodeFormula] at h
 all_goals try { exact False.elim ((sourceNode_ne_zero (by decide)) h) }
 all_goals try { exact False.elim ((sourceNode_ne_zero (by decide)) h.symm) }
 all_goals try { have he := (sourceNode_inj (by decide) (by decide)).mp h; simp_all }
 all_goals try rfl
 all_goals have he := (sourceNode_inj (by decide) (by decide)).mp h
 all_goals simp only [true_and, and_true, eq_self] at he
 all_goals congr 1 <;> first | (apply_assumption; exact he.1) | (apply_assumption; exact he.2) | (apply_assumption; exact he)

/-- Exact Peano cons: successor of right-oriented Cantor pairing. -/
def encodeList (f : α → Nat) : List α → Nat
 | [] => 0
 | x::xs => cantor (f x) (encodeList f xs) + 1

def encodeContext := encodeList encodeFormula

def encodeRow : Row → Nat
 | .seq Γ a => cantor 0 (cantor (encodeContext Γ) (encodeFormula a))
 | .branches Γ a b c => cantor 1 (cantor (encodeContext Γ)
     (cantor (encodeFormula a) (cantor (encodeFormula b) (encodeFormula c))))

def encodeTrace := encodeList encodeRow

theorem encodeList_injective {f : α → Nat} (hf : Function.Injective f) :
 Function.Injective (encodeList f) := by
 intro xs
 induction xs with
 | nil => intro ys h; cases ys <;> simp_all [encodeList]
 | cons x xs ih =>
   intro ys h
   cases ys with
   | nil => simp [encodeList] at h
   | cons y ys =>
     have hp : cantor (f x) (encodeList f xs) = cantor (f y) (encodeList f ys) := by
       simpa only [encodeList, Nat.add_right_cancel_iff] using h
     have hh := cantor_injective hp
     have hx := hf hh.1
     have ht := ih hh.2
     subst_vars
     rfl

theorem encodeContext_injective : Function.Injective encodeContext :=
 encodeList_injective encodeFormula_injective

theorem encodeRow_injective : Function.Injective encodeRow := by
 intro r s h
 cases r <;> cases s <;> simp only [encodeRow] at h
 · have hh := cantor_injective (cantor_injective h).2
   have hc := encodeContext_injective hh.1
   have hf := encodeFormula_injective hh.2
   subst_vars
   rfl
 · have hh := (cantor_injective h).1; omega
 · have hh := (cantor_injective h).1; omega
 · have hh := cantor_injective (cantor_injective h).2
   have ha := cantor_injective hh.2
   have hb := cantor_injective ha.2
   have hΓ := encodeContext_injective hh.1
   have hA := encodeFormula_injective ha.1
   have hB := encodeFormula_injective hb.1
   have hC := encodeFormula_injective hb.2
   subst_vars
   rfl

end ZFR
