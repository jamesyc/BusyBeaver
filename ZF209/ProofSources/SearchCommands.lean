module
public import SearchProvability
@[expose] public section
namespace C209Search
open C209Soundness M6.Source.Cantor M6.Source.Enumeration

structure CommandStore where
  t : Nat
  w : Nat
  d : Nat
  h : Nat
  deriving DecidableEq, Repr

def gate (a d h : Nat) : Nat := if a ≠ d ∧ a ≠ h then pointedGateCode a d h else 0

def heads (a d h oldd oldh : Nat) : List Nat :=
 [head1Code a d h,head2Code a d h,head3Code a d h,
  head4Code a d h,head5Code a d h,head6Code a d h,
  rho8Code a d h oldd,allCode oldd oldh]

def commandEval : Command → CommandStore → Option CommandStore
 | .shift,s => if s.t+s.h=1 then none else
    some ⟨s.h,(M6.Source.Cantor.decode s.w).2,s.d,(M6.Source.Cantor.decode s.w).1⟩
 | .mp x,s => let v := s.d+x
    if impCode s.t v=s.h then some ⟨v,pair 0 s.w,v,0⟩ else some ⟨0,s.w,v,0⟩
 | .ax a x y,s => some ⟨gate a (s.d+x) (s.h+y),
    (heads a (s.d+x) (s.h+y) s.d s.h ++ [s.t]).foldr pair s.w,0,0⟩

def commandsEval : List Command → CommandStore → Option CommandStore
 | [],s => some s
 | c::cs,s => (commandEval c s).bind (commandsEval cs)

def zeroStore : CommandStore := ⟨0,0,0,0⟩

theorem commandsEval_append (xs ys : List Command) (s : CommandStore) :
 commandsEval (xs++ys) s = (commandsEval xs s).bind (commandsEval ys) := by
 induction xs generalizing s with
 | nil => rfl
 | cons c cs ih =>
   simp only [List.cons_append,commandsEval]
   cases h : commandEval c s <;> simp [ih]
end C209Search
