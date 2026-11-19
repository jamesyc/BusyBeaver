module
public import DirectCanonicalUnary
public import DirectCanonicalBinary
public import DirectCanonicalAcceptance
@[expose] public section
namespace RosserDirect.ProofInterpreter
open Turing ContextProgram ZFR
set_option backward.isDefEq.respectTransparency false

def wk_contract (Γ Δ : Context) (a : Formula) (p : Executable.Cert) :
 UnaryContract (.wk Γ Δ a p) p (.seq Γ a) where
 prelude := TokenVM.emitContext Γ ++ TokenVM.emitContext Δ ++ TokenVM.emitFormula a
 operands := [.formula a,.context Δ,.context Γ]
 opcode := 45
 emitted := rfl
 prefix_runs := fun s => ((SyntaxInterpreter.context_runs Γ s).append
   (SyntaxInterpreter.context_runs Δ _)).append (SyntaxInterpreter.formula_runs a _)
 mismatch := by
   intro actual hne v rest rows s
   obtain ⟨w,left,right,h⟩ := reject_wk_premise Γ Δ a actual hne v rest rows s
   exact ⟨_,_,_,_,_,_,h⟩

theorem wk_rejects_subset (Γ Δ : Context) (a : Formula) (p : Executable.Cert)
 (hp : Runs p (.seq Γ a)) (hn : ¬ ∀ f ∈ Γ, f ∈ Δ) : Rejects (.wk Γ Δ a p) := by
 intro s v rest rows
 have hpre := (wk_contract Γ Δ a p).prefix_runs s v
   (payloadBits (TokenVM.emitCert p) ++ tokenBits 45 ++ rest) rows
 have hr := hp ([.formula a,.context Δ,.context Γ] ++ s) none (tokenBits 45 ++ rest) rows
 obtain ⟨vals,tmp,hf⟩ := reject_wk_subset Γ Δ a hn none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hpre hr
 refine ⟨none,rest,vals,[],tmp,rows,?_⟩
 simpa [TM2.Reaches,wk_contract,TokenVM.emitCert,payloadBits,List.flatMap_append,List.append_assoc]
   using hpre.trans (hr.trans hf)

theorem wk_evaluates (Γ Δ : Context) (a : Formula) (p : Executable.Cert)
 (hp : Evaluates p) : Evaluates (.wk Γ Δ a p) := by
 cases hc : Executable.check p with
 | none =>
   have hr : Rejects p := by simpa [Evaluates,hc] using hp
   simpa [Evaluates,Executable.check,Executable.demand,hc]
     using (wk_contract Γ Δ a p).child_reject hr
 | some r =>
   have hr : Runs p r.val := by simpa [Evaluates,hc] using hp
   by_cases he : r.val = Row.seq Γ a
   · by_cases hs : ∀ f ∈ Γ, f ∈ Δ
     · have hh := wk_runs Γ Δ a p hs (he ▸ hr)
       simp only [Evaluates,Executable.check,Executable.demand,hc,he,↓reduceDIte,Bind.bind,Option.bind_some]
       simp only [pure, Bind.bind, Option.bind_some]
       rw [dif_pos hs]
       exact hh
     · have hh := wk_rejects_subset Γ Δ a p (he ▸ hr) hs
       simpa [Evaluates,Executable.check,Executable.demand,hc,he,hs] using hh
   · have hh := (wk_contract Γ Δ a p).wrong_row r.val hr (Ne.symm he)
     simpa [Evaluates,Executable.check,Executable.demand,hc,he] using hh

theorem evaluates_all (p : Executable.Cert) : Evaluates p := by
 induction p with
 | ctx Γ a => exact ctx_evaluates Γ a
 | pc Γ a b => exact pc_evaluates Γ a b
 | ii Γ a b p ih => exact ii_evaluates Γ a b p ih
 | ie Γ a b p q ih jq => exact ie_evaluates Γ a b p q ih jq
 | exp Γ a p ih => exact exp_evaluates Γ a p ih
 | ci Γ a b p q ih jq => exact ci_evaluates Γ a b p q ih jq
 | ce1 Γ a b p ih => exact ce1_evaluates Γ a b p ih
 | ce2 Γ a b p ih => exact ce2_evaluates Γ a b p ih
 | di1 Γ a b p ih => exact di1_evaluates Γ a b p ih
 | di2 Γ a b p ih => exact di2_evaluates Γ a b p ih
 | branchPair Γ a b c p q ih jq => exact branchPair_evaluates Γ a b c p q ih jq
 | de Γ a b c p q ih jq => exact de_evaluates Γ a b c p q ih jq
 | wk Γ Δ a p ih => exact wk_evaluates Γ Δ a p ih
 | allI Γ a p ih => exact allI_evaluates Γ a p ih
 | allE Γ a t p ih => exact allE_evaluates Γ a t p ih
 | exI Γ a t p ih => exact exI_evaluates Γ a t p ih
 | exE Γ a c p q ih jq => exact exE_evaluates Γ a c p q ih jq

end RosserDirect.ProofInterpreter
