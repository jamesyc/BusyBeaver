module
public import I0451.Commands.Symbolic

/-! Decode symbolic outputs into the four-constructor formula syntax
without evaluating the Cantor code of a large expression. -/
@[expose] public section
namespace I0451.Runtime

open I0451.Logic M6.Source.Cantor

def CounterExpr.toFormula : CounterExpr → Option Formula
  | .number 0 | .scaled (.number 0) => some .truth
  | .number 1 | .add (.scaled (.number 0)) (.number 1) => some (.mem 0 0)
  | .scaled (.pair a b) => a.toFormula.bind fun fa => b.toFormula.map (.imp fa)
  | .add (.scaled (.pair (.number a) (.number b))) (.number 1) => some (.mem a b)
  | .add (.scaled (.pair (.number a) b)) (.number 2) => b.toFormula.map (.all a)
  | .add (.scaled (.number 0)) (.number 2) => some (.all 0 .truth)
  | .add (.scaled (.pair (.number a) (.number b))) (.number 3) => some (.equal a b)
  | .add (.scaled (.number 0)) (.number 3) => some (.equal 0 0)
  | _ => none

theorem CounterExpr.toFormula_sound (e : CounterExpr) (input : Registers) (f : Formula)
    (recognized : e.toFormula = some f) : e.eval input = f.code := by
  induction e using CounterExpr.toFormula.induct generalizing f with
  | case1 | case2 | case3 | case4 | case6 | case8 | case9 | case10 =>
    simp only [CounterExpr.toFormula, Option.some.injEq] at recognized
    subst f
    rfl
  | case5 a b ihA ihB =>
    simp only [CounterExpr.toFormula] at recognized
    change (a.toFormula.bind fun fa => b.toFormula.map (Formula.imp fa)) = some f at recognized
    obtain ⟨fa, ra, fb, rb, same⟩ := by
      simpa only [Option.bind_eq_some_iff, Option.map_eq_some_iff] using recognized
    subst f
    simp only [CounterExpr.eval, Formula.code, Logic.imp, ihA _ ra, ihB _ rb]
  | case7 a b ih =>
    simp only [CounterExpr.toFormula, Option.map_eq_some_iff] at recognized
    obtain ⟨fb, rb, rfl⟩ := recognized
    simp only [CounterExpr.eval, Formula.code, Logic.all, ih _ rb]
  | case11 e none => simp [CounterExpr.toFormula] at recognized

end I0451.Runtime
