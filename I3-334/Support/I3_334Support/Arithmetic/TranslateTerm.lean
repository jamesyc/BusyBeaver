module
public import I3_334Support.Arithmetic.OmegaDomain
public import I3_334Support.Arithmetic.SetTemplates
@[expose] public section

namespace PalomarI3380.Logic.Expanded

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open SquareRepresentation

attribute [local irreducible] additionAt multiplicationAt

variable {V : Type} {ξ : Type} {E G : V → V → Prop} {n : Nat}

def Argument.up (a : Argument V) : Argument V := a.rename Nat.succ

/-- Interpret arithmetic terms as their functional graphs over the named set
language. The inputs are already constrained to be natural numbers. -/
def translateTerm : FFL.FirstOrder.Semiterm ℒₒᵣ ξ n →
    (Fin n → Argument V) → (ξ → Argument V) → Argument V → Formula V
  | .bvar i, bound, _, result => .eq result (bound i)
  | .fvar i, _, free, result => .eq result (free i)
  | .func .zero _, _, _, result => numeralAt 0 result
  | .func .one _, _, _, result => numeralAt 1 result
  | .func .add operands, bound, free, result =>
    .ex (.and (translateTerm (operands 0) (Argument.up ∘ bound) (Argument.up ∘ free) (.variable 0))
      (.ex (.and (translateTerm (operands 1) (Argument.up ∘ Argument.up ∘ bound)
        (Argument.up ∘ Argument.up ∘ free) (.variable 0))
        (additionAt (.variable 1) (.variable 0) result.up.up))))
  | .func .mul operands, bound, free, result =>
    .ex (.and (translateTerm (operands 0) (Argument.up ∘ bound) (Argument.up ∘ free) (.variable 0))
      (.ex (.and (translateTerm (operands 1) (Argument.up ∘ Argument.up ∘ bound)
        (Argument.up ∘ Argument.up ∘ free) (.variable 0))
        (multiplicationAt (.variable 1) (.variable 0) result.up.up))))

theorem translateTerm_scope (t : FFL.FirstOrder.Semiterm ℒₒᵣ ξ n)
    {d : Nat} {bound : Fin n → Argument V} {free : ξ → Argument V} {result : Argument V}
    (b : ∀ i, (bound i).bound d) (f : ∀ i, (free i).bound d) (r : result.bound d) :
    Bound (translateTerm t bound free result) d := by
  induction t generalizing d bound free result with
  | bvar i => exact ⟨r,b i⟩
  | fvar i => exact ⟨r,f i⟩
  | func op operands ih =>
    cases op with
    | zero => exact numeralAt_scope r
    | one => exact numeralAt_scope r
    | add | mul =>
      have first := ih 0 (d := d+1) (bound := Argument.up ∘ bound)
        (free := Argument.up ∘ free) (result := .variable 0)
        (fun i => Argument.bound_shift (b i)) (fun i => Argument.bound_shift (f i)) (Nat.zero_lt_succ _)
      have second := ih 1 (d := d+2) (bound := Argument.up ∘ Argument.up ∘ bound)
        (free := Argument.up ∘ Argument.up ∘ free) (result := .variable 0)
        (fun i => Argument.bound_shift (Argument.bound_shift (b i)))
        (fun i => Argument.bound_shift (Argument.bound_shift (f i))) (Nat.zero_lt_succ _)
      have out := Argument.bound_shift (Argument.bound_shift r)
      have left : (Argument.variable (V := V) 1).bound (d+2) := by change 1 < d+2; omega
      have right : (Argument.variable (V := V) 0).bound (d+2) := Nat.zero_lt_succ _
      simp only [translateTerm,Bound]
      refine ⟨first,second,?_⟩
      first
      | case add => exact additionAt_scope left right out
      | case mul => exact multiplicationAt_scope left right out

variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

theorem translateTerm_eval (t : FFL.FirstOrder.Semiterm ℒₒᵣ ξ n)
    (bound : Fin n → Argument V) (free : ξ → Argument V) (out : Argument V) (env : Nat → V)
    (values : Fin n → D.Points) (params : ξ → D.Points)
    (bv : ∀ i, (bound i).value env = (values i).val)
    (fv : ∀ i, (free i).value env = (params i).val) :
    eval E G (translateTerm t bound free out) env ↔ out.value env = (t.val values params).val := by
  induction t generalizing bound free out env with
  | bvar i =>
    change out.value env = (bound i).value env ↔ out.value env = (values i).val
    rw [bv i]
  | fvar i =>
    change out.value env = (free i).value env ↔ out.value env = (params i).val
    rw [fv i]
  | func op operands ih =>
    cases op with
    | zero =>
      exact (numeralAt_eval _ _ _).trans ((L.context inhabited).numeral_def 0 _)
    | one =>
      exact (numeralAt_eval _ _ _).trans ((L.context inhabited).numeral_def 1 _)
    | add | mul =>
      let left := (operands 0).val values params
      let right := (operands 1).val values params
      have first (x : V) := ih 0 (Argument.up ∘ bound) (Argument.up ∘ free) (.variable 0) (pushValue env x)
        (fun i => (Argument.value_shift _ _ _).trans (bv i))
        (fun i => (Argument.value_shift _ _ _).trans (fv i))
      have second (x y : V) := ih 1 (Argument.up ∘ Argument.up ∘ bound) (Argument.up ∘ Argument.up ∘ free)
        (.variable 0) (pushValue (pushValue env x) y)
        (fun i => (Argument.value_shift _ _ _).trans ((Argument.value_shift _ _ _).trans (bv i)))
        (fun i => (Argument.value_shift _ _ _).trans ((Argument.value_shift _ _ _).trans (fv i)))
      simp only [translateTerm,eval,first,second,additionAt_eval,multiplicationAt_eval,Argument.up,Argument.value_shift]
      first
      | case add =>
          change (∃ x, x = left.val ∧ ∃ y, y = right.val ∧ Internal.Add E x y (out.value env)) ↔
            out.value env = (left+right).val
          rw [exists_eq_left,exists_eq_left]
          exact D.add_result left right (out.value env)
      | case mul =>
          change (∃ x, x = left.val ∧ ∃ y, y = right.val ∧ Internal.Mul E x y (out.value env)) ↔
            out.value env = (left*right).val
          rw [exists_eq_left,exists_eq_left]
          exact D.mul_result left right (out.value env)

end PalomarI3380.Logic.Expanded
