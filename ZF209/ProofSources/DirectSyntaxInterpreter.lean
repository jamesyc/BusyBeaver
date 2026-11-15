module
public import DirectContextProgram
@[expose] public section
namespace RosserDirect.SyntaxInterpreter
open Turing ContextProgram ZFR ZFR.TokenVM

/-- Compositional execution contract for token programs. No fixed input size,
execution bound, or runtime call to a Lean syntax operation is assumed. -/
def Runs (tokens : List Nat) (s t : List Value) : Prop :=
 ∀ (v : Option Symbol) (rest rows : List Symbol), TM2.Reaches ContextProgram.machine
   (ContextProgram.cfg (.dispatch .start) v (payloadBits tokens ++ rest) (TypedContext.stack s) [] [] rows)
   (ContextProgram.cfg (.dispatch .start) none rest (TypedContext.stack t) [] [] rows)

theorem Runs.append {xs ys : List Nat} {s u t : List Value}
    (hx : Runs xs s u) (hy : Runs ys u t) : Runs (xs ++ ys) s t := by
 intro v rest rows
 have h := (hx v (payloadBits ys ++ rest) rows).trans (hy none rest rows)
 simpa [TM2.Reaches,payloadBits,List.flatMap_append,List.append_assoc] using h

theorem nat_runs (n : Nat) (s : List Value) : Runs (emitNat n) s (.nat n :: s) := by
 intro v rest rows
 simpa [payloadBits,emitNat] using execute_nat n v rest rows s

theorem bottom_runs (s : List Value) : Runs [1] s (.formula .bot :: s) := by
 intro v rest rows
 simpa [payloadBits] using execute_bottom v rest rows s

theorem atomic_runs (kind : Bool) (a b : Nat) (s : List Value) :
 Runs [if kind then 5 else 3] (.nat b :: .nat a :: s) (.formula (AtomicFormula.formula kind a b) :: s) := by
 intro v rest rows
 simpa [payloadBits] using execute_atomic kind a b v rest rows s

theorem unary_runs (kind : Bool) (f : Formula) (s : List Value) :
 Runs [if kind then 15 else 13] (.formula f :: s) (.formula (unaryFormula kind f) :: s) := by
 intro v rest rows
 simpa [payloadBits] using execute_unary kind f v rest rows s

theorem binary_runs (kind : Fin 3) (p q : Formula) (s : List Value) :
 Runs [7+2*kind.val] (.formula q :: .formula p :: s) (.formula (binaryFormula kind p q) :: s) := by
 intro v rest rows
 simpa [payloadBits] using execute_binary kind p q v rest rows s

theorem empty_runs (s : List Value) : Runs [17] s (.context [] :: s) := by
 intro v rest rows
 simpa [payloadBits] using execute_empty v rest rows s

theorem cons_runs (Γ : Context) (f : Formula) (s : List Value) :
 Runs [19] (.context Γ :: .formula f :: s) (.context (f :: Γ) :: s) := by
 intro v rest rows
 simpa [payloadBits] using execute_cons v rest rows Γ f s

/-- The actual finite interpreter executes every canonical formula program,
including unbounded variable indices and arbitrary nesting. -/
theorem formula_runs (f : Formula) (s : List Value) : Runs (emitFormula f) s (.formula f :: s) := by
 induction f generalizing s with
 | bot => exact bottom_runs s
 | mem a b =>
   simpa [emitFormula,AtomicFormula.formula,List.append_assoc] using
     (nat_runs a s).append ((nat_runs b (.nat a :: s)).append (atomic_runs false a b s))
 | eq a b =>
   simpa [emitFormula,AtomicFormula.formula,List.append_assoc] using
     (nat_runs a s).append ((nat_runs b (.nat a :: s)).append (atomic_runs true a b s))
 | and p q ip iq =>
   simpa [emitFormula,binaryFormula,List.append_assoc] using
     (ip s).append ((iq (.formula p :: s)).append (binary_runs 0 p q s))
 | or p q ip iq =>
   simpa [emitFormula,binaryFormula,List.append_assoc] using
     (ip s).append ((iq (.formula p :: s)).append (binary_runs 1 p q s))
 | imp p q ip iq =>
   simpa [emitFormula,binaryFormula,List.append_assoc] using
     (ip s).append ((iq (.formula p :: s)).append (binary_runs 2 p q s))
 | all p ip =>
   simpa [emitFormula,unaryFormula] using (ip s).append (unary_runs false p s)
 | ex p ip =>
   simpa [emitFormula,unaryFormula] using (ip s).append (unary_runs true p s)

/-- Same source context semantics, revised injective storage representation.
The program is unchanged, so the redesign loses no ZFR formula or context. -/
theorem context_runs (Γ : Context) (s : List Value) : Runs (emitContext Γ) s (.context Γ :: s) := by
 induction Γ generalizing s with
 | nil => exact empty_runs s
 | cons f Γ ih =>
   simpa [emitContext,List.append_assoc] using
     (formula_runs f s).append ((ih (.formula f :: s)).append (cons_runs Γ f s))

end RosserDirect.SyntaxInterpreter
