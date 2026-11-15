module
public import ExactGateSemantics
@[expose] public section
namespace C209Soundness

def ExactAxiom (n : Nat) : Prop :=
  n = 0 ∨ ∃ a d h u : Nat,
    n = head1Code a d h ∨ n = head2Code a d h ∨
    n = head3Code a d h ∨ n = head4Code a d h ∨
    n = head5Code a d h ∨ n = head6Code a d h ∨
    (u ≤ d ∧ n = rho8Code a d h u) ∨
    (a ≠ d ∧ a ≠ h ∧ n = pointedGateCode a d h)

inductive ExactHistory : List Nat → Prop
  | nil : ExactHistory []
  | axRule (n : Nat) (xs : List Nat) : ExactHistory xs → ExactAxiom n → ExactHistory (n :: xs)
  | mp (b c : Nat) (xs : List Nat) :
      ExactHistory xs → b ∈ xs → impCode b c ∈ xs → ExactHistory (c :: xs)
  | gen (i b : Nat) (xs : List Nat) :
      ExactHistory xs → b ∈ xs → ExactHistory (allCode i b :: xs)

def ExactProvable (n : Nat) : Prop := ∃ xs, ExactHistory xs ∧ n ∈ xs

universe u
variable {α : Type u}

end C209Soundness
