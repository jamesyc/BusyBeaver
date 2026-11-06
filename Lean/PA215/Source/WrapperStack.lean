import PA215.Source.Cantor

/-! Explicit finite proved wrappers above an arbitrary opaque numeric tail.
Zero-valued heads and the Cantor zero alias are allowed without exception. -/
namespace PA215.Source.WrapperStack
open Cantor

def encode (heads : List Nat) (tail : Nat) : Nat := heads.foldr pair tail

def Safe (Proved : Nat → Prop) (tail depth stack : Nat) : Prop :=
  ∃ heads : List Nat, heads.length = depth ∧ (∀ x ∈ heads, Proved x) ∧ stack = encode heads tail

theorem empty (P : Nat → Prop) (tail : Nat) : Safe P tail 0 tail := by
  exact ⟨[],rfl,by simp,rfl⟩

theorem push (h : Safe P tail depth stack) (hx : P x) :
    Safe P tail (depth+1) (pair x stack) := by
  rcases h with ⟨heads,hlen,hp,rfl⟩
  refine ⟨x::heads,by simp [hlen],?_,rfl⟩
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact hp y hy

/-- Popping a nonempty safe wrapper layer returns a proved head and preserves
all remaining wrappers over the exact SAME opaque tail. -/
theorem pop (h : Safe P tail (depth+1) stack) :
    P (decode stack).1 ∧ Safe P tail depth (decode stack).2 := by
  rcases h with ⟨heads,hlen,hp,rfl⟩
  cases heads with
  | nil => simp at hlen
  | cons x xs =>
    have hlen' : xs.length = depth := by simp only [List.length_cons] at hlen; omega
    have he : encode (x::xs) tail = pair x (encode xs tail) := rfl
    rw [he,decode_pair]
    exact ⟨hp x (by simp),xs,hlen',fun y hy => hp y (by simp [hy]),rfl⟩

theorem encode_append (xs ys : List Nat) (tail : Nat) :
    encode (xs++ys) tail = encode xs (encode ys tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [encode,List.cons_append,List.foldr_cons] using congrArg (pair x) ih

theorem prepend (hs : ∀ x ∈ heads, P x) (h : Safe P tail depth stack) :
    Safe P tail (heads.length+depth) (encode heads stack) := by
  rcases h with ⟨old,hlen,hp,rfl⟩
  refine ⟨heads++old,by simp [hlen],?_,(encode_append heads old tail).symm⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hs x hx
  · exact hp x hx

/-- The unproved initial saved T=1 over W=1 is quarantined in opaque tail4.
Only the nine newly produced AX heads are claimed to be proved wrappers. -/
theorem initial_nine (hlen : heads.length = 9) (hp : ∀ x ∈ heads, P x) :
    Safe P 4 9 (encode (heads++[1]) 1) := by
  refine ⟨heads,hlen,hp,?_⟩
  rw [encode_append]
  rfl

#print axioms pop
#print axioms prepend
#print axioms initial_nine
end PA215.Source.WrapperStack
