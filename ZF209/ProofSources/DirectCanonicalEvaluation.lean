module
public import DirectPartialProofInterpreter
@[expose] public section
namespace RosserDirect.ProofInterpreter
open Turing ContextProgram ZFR
set_option backward.isDefEq.respectTransparency false

/-- A failed canonical candidate reaches the designated reject label. Residual
program and stacks are deliberately existential: failure in a child can occur
before the parent's opcode, with its pending operands still present. -/
def Rejects (p : Executable.Cert) : Prop :=
 ∀ (s : List TokenVM.Value) (v : Option Symbol) (rest rows : List Symbol),
 ∃ w program vals scratch temporary output,
 TM2.Reaches ContextProgram.machine
 (ContextProgram.cfg (.dispatch .start) v (payloadBits (TokenVM.emitCert p) ++ rest)
   (TypedContext.stack s) [] [] rows)
 (ContextProgram.cfg .proofReject w program vals scratch temporary output)

/-- Exact canonical evaluation, including unsuccessful certificates, not merely
completeness for certificates obtained from pre-existing derivations. -/
def Evaluates (p : Executable.Cert) : Prop :=
 match Executable.check p with
 | none => Rejects p
 | some r => Runs p r.val

theorem ctx_evaluates (Γ : Context) (a : Formula) : Evaluates (.ctx Γ a) := by
 by_cases h : a ∈ Γ
 · simpa [Evaluates,Executable.check,h] using ctx_runs Γ a h
 · simp only [Evaluates,Executable.check,dif_neg h]
   intro s v rest rows
   obtain ⟨tmp, ht⟩ := reject_ctx_program Γ a h v rest rows s
   exact ⟨none,rest,_,[],tmp,_,ht⟩

theorem pc_evaluates (Γ : Context) (a b : Formula) : Evaluates (.pc Γ a b) :=
 pc_runs Γ a b

/-- An early child rejection propagates through canonical argument emission. -/
theorem exp_rejects_child (Γ : Context) (a : Formula) (p : Executable.Cert)
 (hp : Rejects p) : Rejects (.exp Γ a p) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 29 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ tokenBits 29 ++ rest) rows
 obtain ⟨w,program,vals,scratch,tmp,out,hr⟩ :=
   hp (.formula a :: .context Γ :: s) none (tokenBits 29 ++ rest) rows
 refine ⟨w,program,vals,scratch,tmp,out,?_⟩
 simp only [TM2.Reaches,List.append_assoc] at hg ha hr
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc]
   using hg.trans (ha.trans hr)

/-- A child may execute successfully but return the wrong premise row. -/
theorem exp_rejects_mismatch (Γ : Context) (a : Formula) (p : Executable.Cert)
 (r : Row) (hp : Runs p r) (hne : Row.seq Γ .bot ≠ r) : Rejects (.exp Γ a p) := by
 intro s v rest rows
 have hg := SyntaxInterpreter.context_runs Γ s v
   (payloadBits (TokenVM.emitFormula a) ++ payloadBits (TokenVM.emitCert p) ++ tokenBits 29 ++ rest) rows
 have ha := SyntaxInterpreter.formula_runs a (.context Γ :: s) none
   (payloadBits (TokenVM.emitCert p) ++ tokenBits 29 ++ rest) rows
 have hr := hp (.formula a :: .context Γ :: s) none (tokenBits 29 ++ rest) rows
 obtain ⟨w,left,right,he⟩ := reject_exp Γ a r hne none rest rows s
 refine ⟨w,rest,left,[],[],right,?_⟩
 simp only [TM2.Reaches,List.append_assoc] at hg ha hr he
 simpa [TM2.Reaches,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc]
   using hg.trans (ha.trans (hr.trans he))

theorem exp_evaluates (Γ : Context) (a : Formula) (p : Executable.Cert)
 (hp : Evaluates p) : Evaluates (.exp Γ a p) := by
 cases hc : Executable.check p with
 | none =>
   have hr : Rejects p := by simpa [Evaluates,hc] using hp
   simpa [Evaluates,Executable.check,Executable.demand,hc] using exp_rejects_child Γ a p hr
 | some r =>
   have hr : Runs p r.val := by simpa [Evaluates,hc] using hp
   by_cases he : r.val = Row.seq Γ .bot
   · have hh := exp_runs Γ a p (he ▸ hr)
     simpa [Evaluates,Executable.check,Executable.demand,hc,he] using hh
   · have hh := exp_rejects_mismatch Γ a p r.val hr (Ne.symm he)
     simpa [Evaluates,Executable.check,Executable.demand,hc,he] using hh

/-- An unbounded nested certificate sublanguage with full rejection behavior.
Other constructors require analogous compositions before general soundness. -/
inductive Core : Executable.Cert → Prop
 | ctx (Γ a) : Core (.ctx Γ a)
 | pc (Γ a b) : Core (.pc Γ a b)
 | exp (Γ a p) : Core p → Core (.exp Γ a p)

end RosserDirect.ProofInterpreter
