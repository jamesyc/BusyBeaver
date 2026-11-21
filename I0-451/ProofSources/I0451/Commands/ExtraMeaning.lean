module
public import I0451.Commands.ExtraCommand
public import I0451.Commands.FormulaOutput
public import I0451.Logic.NormalForm
public import I0451.Logic.SetSentences

/-! Identify the literal emitted formulas up to capture-free naming and
propositional normalization. The check computes on syntax alone. -/
@[expose] public section
namespace I0451.Runtime

open I0451.Logic

def matchesFormula (output : CounterExpr) (spec : Formula) : Bool :=
  output.toFormula.any fun f => decide (f.normalize [] true = spec.normalize [] true)

theorem matchesFormula_sound {output : CounterExpr} {spec : Formula}
    (checked : matchesFormula output spec = true) (input : Registers)
    {V : Type} (E : V → V → Prop) (irrefl : ∀ x, ¬ E x x) (s : Nat → V) :
    Eval E s (output.eval input) ↔ spec.eval E s := by
  unfold matchesFormula at checked
  cases decoded : output.toFormula with
  | none => simp [decoded] at checked
  | some f =>
    have eq : f.normalize [] true = spec.normalize [] true := by simpa [decoded] using checked
    rw [output.toFormula_sound input f decoded, eval_formula]
    exact Formula.equiv_of_normalize eq E irrefl s

set_option maxRecDepth 16000 in
set_option maxHeartbeats 13000000 in
theorem actual_foundation_checked : matchesFormula literalFoundationTerm SetSentences.foundationFormula = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 13000000 in
theorem actual_berkeley_checked : matchesFormula literalBerkeleyTerm SetSentences.berkeleyFormula = true := by
  decide +kernel

theorem literal_foundation_eval {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (s : Nat → V) : Eval E s literalFoundationCode ↔ SetSentences.Foundation E := by
  have aligned := matchesFormula_sound actual_foundation_checked (fun _ => 0) E irrefl s
  exact aligned.trans ((eval_formula E _ _).symm.trans (SetSentences.foundation_eval irrefl s))

theorem literal_berkeley_eval {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (s : Nat → V) : Eval E s literalBerkeleyCode ↔ SetSentences.BerkeleyFormula E := by
  have aligned := matchesFormula_sound actual_berkeley_checked (fun _ => 0) E irrefl s
  exact aligned.trans ((eval_formula E _ _).symm.trans (SetSentences.berkeley_formula_eval irrefl s))

end I0451.Runtime
