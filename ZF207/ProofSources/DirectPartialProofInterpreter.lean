module
public import DirectCtxProofRule
public import DirectExpProofRule
public import DirectConjunctionRule
public import DirectRightConjunctionRule
public import DirectPeirceRule
public import DirectImpIntroRule
public import DirectConjIntroRule
public import DirectImpElimRule
public import DirectBranchPairRule
public import DirectDisjElimRule
public import DirectWeakeningRule
public import DirectAllIntroRule
public import DirectQuantifierRules
public import DirectExistsElimRule
@[expose] public section
namespace RosserDirect.ProofInterpreter
open Turing ContextProgram ZFR

/-- Semantic certificate execution, preserving all surrounding stacks. This is a
property to be proved per rule, not an axiom asserting the remaining rules. -/
def Runs (p : Executable.Cert) (r : Row) : Prop :=
 ∀ (s : List TokenVM.Value) (v : Option Symbol) (rest rows : List Symbol),
 TM2.Reaches ContextProgram.machine
 (ContextProgram.cfg (.dispatch .start) v (payloadBits (TokenVM.emitCert p) ++ rest) (TypedContext.stack s) [] [] rows)
 (ContextProgram.cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode r ++ rows))

theorem ctx_runs (Γ : Context) (f : Formula) (h : f ∈ Γ) : Runs (.ctx Γ f) (.seq Γ f) := by
 intro s v rest rows
 exact execute_ctx_program Γ f h v rest rows s

/-- Verified compositional explosion, including the source assembler order:
arguments, recursive premise certificate, then opcode. -/
theorem exp_runs (Γ : Context) (f : Formula) (p : Executable.Cert)
 (hp : Runs p (.seq Γ .bot)) : Runs (.exp Γ f p) (.seq Γ f) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula f) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 29 ++ rest) rows
 have hf := SyntaxInterpreter.formula_runs f (.context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ tokenBits 29 ++ rest) rows
 have hpr := hp (.formula f :: .context Γ :: s) none (tokenBits 29 ++ rest) rows
 have he := execute_exp Γ f none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hg hf hpr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
   hg.trans (hf.trans (hpr.trans he))

/-- Compositional execution including both formula fields and the recursively
verified premise. -/
theorem di1_runs (Γ : Context) (a b : Formula) (p : Executable.Cert)
 (hp : Runs p (.seq Γ a)) : Runs (.di1 Γ a b p) (.seq Γ (.or a b)) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 37 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
   (payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 37 ++ rest) rows
 have hb := SyntaxInterpreter.formula_runs b (.formula a :: .context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ tokenBits 37 ++ rest) rows
 have hpr := hp (.formula b :: .formula a :: .context Γ :: s) none (tokenBits 37 ++ rest) rows
 have he := execute_di1 Γ a b none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hg ha hb hpr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
   hg.trans (ha.trans (hb.trans (hpr.trans he)))

/-- Compositional execution including both formula fields and the recursively
verified premise. -/
theorem ce1_runs (Γ : Context) (a b : Formula) (p : Executable.Cert)
 (hp : Runs p (.seq Γ (.and a b))) : Runs (.ce1 Γ a b p) (.seq Γ a) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 33 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
   (payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 33 ++ rest) rows
 have hb := SyntaxInterpreter.formula_runs b (.formula a :: .context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ tokenBits 33 ++ rest) rows
 have hpr := hp (.formula b :: .formula a :: .context Γ :: s) none (tokenBits 33 ++ rest) rows
 have he := execute_ce1 Γ a b none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hg ha hb hpr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
   hg.trans (ha.trans (hb.trans (hpr.trans he)))

theorem di2_runs (Γ : Context) (a b : Formula) (p : Executable.Cert)
 (hp : Runs p (.seq Γ b)) : Runs (.di2 Γ a b p) (.seq Γ (.or a b)) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 39 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
   (payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 39 ++ rest) rows
 have hb := SyntaxInterpreter.formula_runs b (.formula a :: .context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ tokenBits 39 ++ rest) rows
 have hpr := hp (.formula b :: .formula a :: .context Γ :: s) none (tokenBits 39 ++ rest) rows
 have he := execute_di2 Γ a b none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hg ha hb hpr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
   hg.trans (ha.trans (hb.trans (hpr.trans he)))

theorem ce2_runs (Γ : Context) (a b : Formula) (p : Executable.Cert)
 (hp : Runs p (.seq Γ (.and a b))) : Runs (.ce2 Γ a b p) (.seq Γ b) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 35 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
   (payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 35 ++ rest) rows
 have hb := SyntaxInterpreter.formula_runs b (.formula a :: .context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ tokenBits 35 ++ rest) rows
 have hpr := hp (.formula b :: .formula a :: .context Γ :: s) none (tokenBits 35 ++ rest) rows
 have he := execute_ce2 Γ a b none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hg ha hb hpr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
   hg.trans (ha.trans (hb.trans (hpr.trans he)))



/-- Canonical Peirce certificate execution, including all syntax operands. -/
theorem pc_runs (Γ : Context) (a b : Formula) :
 Runs (.pc Γ a b) (.seq Γ (.imp (.imp (.imp a b) a) a)) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitFormula b) ++ tokenBits 23 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
   (payloadBits (TokenVM.emitFormula b) ++ tokenBits 23 ++ rest) rows
 have hb := SyntaxInterpreter.formula_runs b (.formula a :: .context Γ :: s) none
   (tokenBits 23 ++ rest) rows
 have hc := execute_pc Γ a b none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hg ha hb hc
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
   hg.trans (ha.trans (hb.trans hc))

theorem ii_runs (Γ : Context) (a b : Formula) (p : Executable.Cert)
 (hp : Runs p (.seq (a :: Γ) b)) : Runs (.ii Γ a b p) (.seq Γ (.imp a b)) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 25 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
   (payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 25 ++ rest) rows
 have hb := SyntaxInterpreter.formula_runs b (.formula a :: .context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ tokenBits 25 ++ rest) rows
 have hpr := hp (.formula b :: .formula a :: .context Γ :: s) none (tokenBits 25 ++ rest) rows
 have he := execute_ii Γ a b none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hg ha hb hpr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
   hg.trans (ha.trans (hb.trans (hpr.trans he)))



/-- Both recursive premise certificates execute in assembler order; the machine
checks their resulting rows in reverse stack order before committing Γ ⊢ a ∧ b. -/
theorem ci_runs (Γ : Context) (a b : Formula) (p q : Executable.Cert)
 (hp : Runs p (.seq Γ a)) (hq : Runs q (.seq Γ b)) :
 Runs (.ci Γ a b p q) (.seq Γ (.and a b)) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 31 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
   (payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 31 ++ rest) rows
 have hb := SyntaxInterpreter.formula_runs b (.formula a :: .context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 31 ++ rest) rows
 have hpr := hp (.formula b :: .formula a :: .context Γ :: s) none (payloadBits (TokenVM.emitCert q) ++ tokenBits 31 ++ rest) rows
 have hqr := hq (.formula b :: .formula a :: .context Γ :: s) none (tokenBits 31 ++ rest) (FramedRow.encode (.seq Γ a) ++ rows)
 have he := execute_ci Γ a b none rest rows s
 simp only [TM2.Reaches,RowPairEquality.rows,List.append_assoc] at hg ha hb hpr hqr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
   hg.trans (ha.trans (hb.trans (hpr.trans (hqr.trans he))))

theorem ie_runs (Γ : Context) (a b : Formula) (p q : Executable.Cert)
 (hp : Runs p (.seq Γ (.imp a b))) (hq : Runs q (.seq Γ a)) :
 Runs (.ie Γ a b p q) (.seq Γ b) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 27 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
   (payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 27 ++ rest) rows
 have hb := SyntaxInterpreter.formula_runs b (.formula a :: .context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 27 ++ rest) rows
 have hpr := hp (.formula b :: .formula a :: .context Γ :: s) none (payloadBits (TokenVM.emitCert q) ++ tokenBits 27 ++ rest) rows
 have hqr := hq (.formula b :: .formula a :: .context Γ :: s) none (tokenBits 27 ++ rest) (FramedRow.encode (.seq Γ (.imp a b)) ++ rows)
 have he := execute_ie Γ a b none rest rows s
 simp only [TM2.Reaches,RowPairEquality.rows,List.append_assoc] at hg ha hb hpr hqr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
   hg.trans (ha.trans (hb.trans (hpr.trans (hqr.trans he))))



/-- Two branch derivations are validated under their respective extended contexts
before the machine commits the exact branch-pair row. -/
theorem branchPair_runs (Γ : Context) (a b c : Formula) (p q : Executable.Cert)
 (hp : Runs p (.seq (a :: Γ) c)) (hq : Runs q (.seq (b :: Γ) c)) :
 Runs (.branchPair Γ a b c p q) (.branches Γ a b c) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitFormula c) ++ payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 41 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
   (payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitFormula c) ++ payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 41 ++ rest) rows
 have hb := SyntaxInterpreter.formula_runs b (.formula a :: .context Γ :: s) none
   (payloadBits (TokenVM.emitFormula c) ++ payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 41 ++ rest) rows
 have hc := SyntaxInterpreter.formula_runs c (.formula b :: .formula a :: .context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 41 ++ rest) rows
 have hpr := hp (.formula c :: .formula b :: .formula a :: .context Γ :: s) none (payloadBits (TokenVM.emitCert q) ++ tokenBits 41 ++ rest) rows
 have hqr := hq (.formula c :: .formula b :: .formula a :: .context Γ :: s) none (tokenBits 41 ++ rest) (FramedRow.encode (.seq (a :: Γ) c) ++ rows)
 have he := execute_branchPair Γ a b c none rest rows s
 simp only [TM2.Reaches,RowPairEquality.rows,List.append_assoc] at hg ha hb hc hpr hqr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
   hg.trans (ha.trans (hb.trans (hc.trans (hpr.trans (hqr.trans he)))))

theorem de_runs (Γ : Context) (a b c : Formula) (p q : Executable.Cert)
 (hp : Runs p (.seq Γ (.or a b))) (hq : Runs q (.branches Γ a b c)) :
 Runs (.de Γ a b c p q) (.seq Γ c) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitFormula c) ++ payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 43 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
   (payloadBits (TokenVM.emitFormula b) ++ payloadBits (TokenVM.emitFormula c) ++ payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 43 ++ rest) rows
 have hb := SyntaxInterpreter.formula_runs b (.formula a :: .context Γ :: s) none
   (payloadBits (TokenVM.emitFormula c) ++ payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 43 ++ rest) rows
 have hc := SyntaxInterpreter.formula_runs c (.formula b :: .formula a :: .context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 43 ++ rest) rows
 have hpr := hp (.formula c :: .formula b :: .formula a :: .context Γ :: s) none (payloadBits (TokenVM.emitCert q) ++ tokenBits 43 ++ rest) rows
 have hqr := hq (.formula c :: .formula b :: .formula a :: .context Γ :: s) none (tokenBits 43 ++ rest) (FramedRow.encode (.seq Γ (.or a b)) ++ rows)
 have he := execute_de Γ a b c none rest rows s
 simp only [TM2.Reaches,RowPairEquality.rows,List.append_assoc] at hg ha hb hc hpr hqr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
   hg.trans (ha.trans (hb.trans (hc.trans (hpr.trans (hqr.trans he)))))



/-- Weakening uses both an exactly matched premise and a finite context-inclusion
check; no subset oracle or side-condition axiom is used at runtime. -/
theorem wk_runs (Γ Δ : Context) (a : Formula) (p : Executable.Cert)
 (sub : ∀ f ∈ Γ, f ∈ Δ) (hp : Runs p (.seq Γ a)) :
 Runs (.wk Γ Δ a p) (.seq Δ a) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitContext Δ) ++ payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 45 ++ rest) rows
 have hd := SyntaxInterpreter.context_runs Δ (.context Γ :: s) none
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 45 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Δ :: .context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ tokenBits 45 ++ rest) rows
 have hpr := hp (.formula a :: .context Δ :: .context Γ :: s) none (tokenBits 45 ++ rest) rows
 have he := execute_wk Γ Δ a sub none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hg hd ha hpr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
   hg.trans (hd.trans (ha.trans (hpr.trans he)))
theorem allI_runs (Γ : Context) (a : Formula) (p : Executable.Cert)
 (hp : Runs p (.seq (shiftContext Γ) a)) : Runs (.allI Γ a p) (.seq Γ (.all a)) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
  (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 47 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
  (payloadBits (TokenVM.emitCert p) ++ tokenBits 47 ++ rest) rows
 have hpr := hp (.formula a :: .context Γ :: s) none (tokenBits 47 ++ rest) rows
 have he := execute_allI Γ a none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hg ha hpr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
  hg.trans (ha.trans (hpr.trans he))


theorem allE_runs (Γ : Context) (a : Formula) (t : Nat) (p : Executable.Cert)
 (hp : Runs p (.seq Γ (.all a))) : Runs (.allE Γ a t p) (.seq Γ (subst t a)) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
  (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitNat t) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 49 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
  (payloadBits (TokenVM.emitNat t) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 49 ++ rest) rows
 have ht := SyntaxInterpreter.nat_runs t (.formula a :: .context Γ :: s) none
  (payloadBits (TokenVM.emitCert p) ++ tokenBits 49 ++ rest) rows
 have hpr := hp (.nat t :: .formula a :: .context Γ :: s) none (tokenBits 49 ++ rest) rows
 have he := execute_quantifier false Γ a t none rest rows s
 simp only [TM2.Reaches,qePremise,qeResult,Bool.false_eq_true,↓reduceIte,List.append_assoc] at hg ha ht hpr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
  hg.trans (ha.trans (ht.trans (hpr.trans he)))

theorem exI_runs (Γ : Context) (a : Formula) (t : Nat) (p : Executable.Cert)
 (hp : Runs p (.seq Γ (subst t a))) : Runs (.exI Γ a t p) (.seq Γ (.ex a)) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
  (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitNat t) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 51 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
  (payloadBits (TokenVM.emitNat t) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 51 ++ rest) rows
 have ht := SyntaxInterpreter.nat_runs t (.formula a :: .context Γ :: s) none
  (payloadBits (TokenVM.emitCert p) ++ tokenBits 51 ++ rest) rows
 have hpr := hp (.nat t :: .formula a :: .context Γ :: s) none (tokenBits 51 ++ rest) rows
 have he := execute_quantifier true Γ a t none rest rows s
 simp only [TM2.Reaches,qePremise,qeResult,Bool.false_eq_true,↓reduceIte,List.append_assoc] at hg ha ht hpr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
  hg.trans (ha.trans (ht.trans (hpr.trans he)))

theorem exE_runs (Γ : Context) (a c : Formula) (p q : Executable.Cert)
 (hp : Runs p (.seq Γ (.ex a))) (hq : Runs q (.seq (a :: shiftContext Γ) (shift c))) :
 Runs (.exE Γ a c p q) (.seq Γ c) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
  (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitFormula c) ++ payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 53 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
  (payloadBits (TokenVM.emitFormula c) ++ payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 53 ++ rest) rows
 have hc := SyntaxInterpreter.formula_runs c (.formula a :: .context Γ :: s) none
  (payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits 53 ++ rest) rows
 have hpr := hp (.formula c :: .formula a :: .context Γ :: s) none (payloadBits (TokenVM.emitCert q) ++ tokenBits 53 ++ rest) rows
 have hqr := hq (.formula c :: .formula a :: .context Γ :: s) none (tokenBits 53 ++ rest) (FramedRow.encode (.seq Γ (.ex a)) ++ rows)
 have he := execute_exE Γ a c none rest rows s
 simp only [TM2.Reaches,RowPairEquality.rows,List.append_assoc] at hg ha hc hpr hqr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc] using
  hg.trans (ha.trans (hc.trans (hpr.trans (hqr.trans he))))
end RosserDirect.ProofInterpreter
