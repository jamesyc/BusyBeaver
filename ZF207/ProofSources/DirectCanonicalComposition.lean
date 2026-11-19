module
public import DirectCanonicalEvaluation
@[expose] public section
namespace RosserDirect.ProofInterpreter
open Turing ContextProgram ZFR
set_option backward.isDefEq.respectTransparency false

abbrev RejectTrace (start : TM2.Cfg (fun _ : GlobalStack => Symbol) Control (Option Symbol)) :=
 ∃ w program vals scratch temporary output,
 TM2.Reaches ContextProgram.machine start (ContextProgram.cfg .proofReject w program vals scratch temporary output)

theorem RejectTrace.prepend {a b} (h : TM2.Reaches ContextProgram.machine a b)
 (hb : RejectTrace b) : RejectTrace a := by
 obtain ⟨w,p,v,s,t,o,hh⟩ := hb
 exact ⟨w,p,v,s,t,o,h.trans hh⟩

structure UnaryContract (parent child : Executable.Cert) (expected : Row) where
 prelude : List Nat
 operands : List TokenVM.Value
 opcode : Nat
 emitted : TokenVM.emitCert parent = prelude ++ TokenVM.emitCert child ++ [opcode]
 prefix_runs : ∀ s, SyntaxInterpreter.Runs prelude s (operands ++ s)
 mismatch : ∀ (actual : Row), expected ≠ actual → ∀ v rest rows s,
   RejectTrace (ContextProgram.cfg (.dispatch .start) v (tokenBits opcode ++ rest)
     (TypedContext.stack (operands ++ s)) [] [] (FramedRow.encode actual ++ rows))

theorem UnaryContract.child_reject {c p e} (u : UnaryContract c p e)
 (hp : Rejects p) : Rejects c := by
 intro s v rest rows
 have hpre := u.prefix_runs s v (payloadBits (TokenVM.emitCert p) ++ tokenBits u.opcode ++ rest) rows
 have hr := hp (u.operands ++ s) none (tokenBits u.opcode ++ rest) rows
 simp only [TM2.Reaches,List.append_assoc] at hpre hr
 have h := RejectTrace.prepend hpre hr
 simpa [RejectTrace,u.emitted,payloadBits,List.flatMap_append,List.append_assoc] using h

theorem UnaryContract.wrong_row {c p e} (u : UnaryContract c p e)
 (r : Row) (hp : Runs p r) (hne : e ≠ r) : Rejects c := by
 intro s v rest rows
 have hpre := u.prefix_runs s v (payloadBits (TokenVM.emitCert p) ++ tokenBits u.opcode ++ rest) rows
 have hr := hp (u.operands ++ s) none (tokenBits u.opcode ++ rest) rows
 have hf := u.mismatch r hne none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hpre hr
 have h := RejectTrace.prepend hpre (RejectTrace.prepend hr hf)
 simpa [RejectTrace,u.emitted,payloadBits,List.flatMap_append,List.append_assoc] using h

theorem unary_evaluates {c p : Executable.Cert} {expected result : Row}
 (u : UnaryContract c p expected) (build : ND expected → ND result)
 (hcheck : Executable.check c = do
   let hp ← Executable.demand (Executable.check p) expected
   pure ⟨result,build hp.down⟩)
 (success : Runs p expected → Runs c result)
 (hp : Evaluates p) : Evaluates c := by
 cases hc : Executable.check p with
 | none =>
   have hr : Rejects p := by simpa [Evaluates,hc] using hp
   simpa [Evaluates,hcheck,Executable.demand,hc] using u.child_reject hr
 | some r =>
   have hr : Runs p r.val := by simpa [Evaluates,hc] using hp
   by_cases he : r.val = expected
   · have hh := success (he ▸ hr)
     simpa [Evaluates,hcheck,Executable.demand,hc,he] using hh
   · have hh := u.wrong_row r.val hr (Ne.symm he)
     simpa [Evaluates,hcheck,Executable.demand,hc,he] using hh

/-- Common operand prelude for propositional unary rules. -/
theorem context_two_formulas (Γ : Context) (a b : Formula) (s : List TokenVM.Value) :
 SyntaxInterpreter.Runs (TokenVM.emitContext Γ ++ TokenVM.emitFormula a ++ TokenVM.emitFormula b)
 s ([.formula b,.formula a,.context Γ] ++ s) :=
 ((SyntaxInterpreter.context_runs Γ s).append (SyntaxInterpreter.formula_runs a _)).append
   (SyntaxInterpreter.formula_runs b _)

end RosserDirect.ProofInterpreter
