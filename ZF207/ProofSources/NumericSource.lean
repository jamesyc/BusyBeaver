module
public import SourceEncoding
public import ComputableDecoding
@[expose] public section
namespace ZFR
open C207Soundness

theorem sourceUnpair_pair (a b : Nat) : unpair (cantor a b) = (a,b) := by
 have h := cantor_injective (unpair_spec (cantor a b))
 exact Prod.ext h.1 h.2

/-- Independent total decoding of the exact Peano cons-list coding. -/
def decodeSourceList (n : Nat) : List Nat :=
 if h : n = 0 then [] else
 let p := unpair (n-1)
 p.1 :: decodeSourceList p.2
termination_by n
decreasing_by
 have hh := unpair_right_le (n-1)
 omega

theorem decodeSourceList_zero : decodeSourceList 0 = [] := by
 rw [decodeSourceList]; simp

theorem decodeSourceList_cons (a b : Nat) :
 decodeSourceList (cantor a b + 1) = a :: decodeSourceList b := by
 rw [decodeSourceList]
 simp [sourceUnpair_pair]

theorem decodeSourceList_encode (f : α → Nat) (xs : List α) :
 decodeSourceList (encodeList f xs) = xs.map f := by
 induction xs with
 | nil => exact decodeSourceList_zero
 | cons x xs ih => simpa only [encodeList, decodeSourceList_cons, List.map_cons, ih]

def sourceMember (a l : Nat) : Prop := a ∈ decodeSourceList l

theorem sourceMember_encode_iff {f : α → Nat} (hf : Function.Injective f) (x : α) (xs : List α) :
 sourceMember (f x) (encodeList f xs) ↔ x ∈ xs := by
 simp only [sourceMember, decodeSourceList_encode, List.mem_map]
 constructor
 · rintro ⟨y,hy,he⟩
   have hxy := hf he
   subst y
   exact hy
 · intro hx; exact ⟨x,hx,rfl⟩

/-- Exact sfAllowed/sfWf recursion, independently defined on all natural codes.
The predecessor bounds in MM0's sfPrevious are automatic from n/8<n. -/
def sourceWf (n : Nat) : Prop :=
 if h : n = 0 then True else
 let t := n % 8
 let p := unpair (n / 8)
 (t = 1 ∨ t = 2) ∨
 ((t = 3 ∨ t = 4 ∨ t = 5) ∧ sourceWf p.1 ∧ sourceWf p.2) ∨
 ((t = 6 ∨ t = 7) ∧ p.2 = 0 ∧ sourceWf p.1)
termination_by n
decreasing_by
 all_goals
   have hq : n/8 < n := Nat.div_lt_self (by omega) (by omega)
   have ha := unpair_left_le (n/8)
   have hb := unpair_right_le (n/8)
   omega

theorem sourceWf_zero : sourceWf 0 := by rw [sourceWf]; trivial

theorem sourceWf_node (t a b : Nat) (ht : t < 8) (hp : 0 < t) :
 sourceWf (sourceNode t a b) ↔
 (t = 1 ∨ t = 2) ∨
 ((t = 3 ∨ t = 4 ∨ t = 5) ∧ sourceWf a ∧ sourceWf b) ∨
 ((t = 6 ∨ t = 7) ∧ b = 0 ∧ sourceWf a) := by
 rw [sourceWf]
 simp only [sourceNode_ne_zero hp, dite_false, sourceNode_tag ht,
   sourceNode_payload ht, sourceUnpair_pair, Prod.fst, Prod.snd]

theorem sourceWf_encodeFormula (a : Formula) : sourceWf (encodeFormula a) := by
 induction a <;> simp only [encodeFormula]
 · exact sourceWf_zero
 all_goals rw [sourceWf_node _ _ _ (by decide) (by decide)]
 all_goals simp_all

def sourceContextWf (Γ : Nat) := ∀ a, sourceMember a Γ → sourceWf a

def sourceContextSub (Γ Δ : Nat) := ∀ a, sourceMember a Γ → sourceMember a Δ

theorem sourceContextWf_encode (Γ : Context) : sourceContextWf (encodeContext Γ) := by
 intro a ha
 simp only [sourceMember, encodeContext, decodeSourceList_encode, List.mem_map] at ha
 obtain ⟨b,_,rfl⟩ := ha
 exact sourceWf_encodeFormula b

theorem sourceContextSub_encode_iff (Γ Δ : Context) :
 sourceContextSub (encodeContext Γ) (encodeContext Δ) ↔ ContextSub Γ Δ := by
 constructor
 · intro h a ha
   exact (sourceMember_encode_iff encodeFormula_injective a Δ).mp
     (h _ ((sourceMember_encode_iff encodeFormula_injective a Γ).mpr ha))
 · intro h a ha
   simp only [sourceMember, encodeContext, decodeSourceList_encode, List.mem_map] at ha ⊢
   obtain ⟨b,hb,rfl⟩ := ha
   exact ⟨b,h b hb,rfl⟩

/-- Exact source_contexts.mm0 row guard, independent of typed rows. -/
def sourceRowWf (r : Nat) : Prop :=
 let p := unpair r
 let q := unpair p.2
 if p.1 = 0 then sourceContextWf q.1 ∧ sourceWf q.2
 else p.1 = 1 ∧ sourceContextWf q.1 ∧
   sourceWf (unpair q.2).1 ∧ sourceWf (unpair (unpair q.2).2).1 ∧
   sourceWf (unpair (unpair q.2).2).2

theorem sourceRowWf_encode (r : Row) : sourceRowWf (encodeRow r) := by
 cases r <;> simp only [encodeRow, sourceRowWf, sourceUnpair_pair, Prod.fst, Prod.snd]
 all_goals simp [sourceContextWf_encode, sourceWf_encodeFormula]

end ZFR
