module
public import DirectCanonicalComposition
@[expose] public section
namespace RosserDirect.ProofInterpreter
open Turing ContextProgram ZFR
set_option backward.isDefEq.respectTransparency false

structure BinaryContract (parent first second : Executable.Cert) (e₁ e₂ : Row) where
 prelude : List Nat
 operands : List TokenVM.Value
 opcode : Nat
 emitted : TokenVM.emitCert parent = prelude ++ TokenVM.emitCert first ++ TokenVM.emitCert second ++ [opcode]
 prefix_runs : ∀ s, SyntaxInterpreter.Runs prelude s (operands ++ s)
 mismatch : ∀ (r₁ r₂ : Row), ¬(e₂ = r₂ ∧ e₁ = r₁) → ∀ v rest rows s,
   RejectTrace (ContextProgram.cfg (.dispatch .start) v (tokenBits opcode ++ rest)
     (TypedContext.stack (operands ++ s)) [] [] (FramedRow.encode r₂ ++ FramedRow.encode r₁ ++ rows))

theorem BinaryContract.first_reject {c p q e₁ e₂} (u : BinaryContract c p q e₁ e₂)
 (hp : Rejects p) : Rejects c := by
 intro s v rest rows
 have hpre := u.prefix_runs s v (payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits u.opcode ++ rest) rows
 have hr := hp (u.operands ++ s) none (payloadBits (TokenVM.emitCert q) ++ tokenBits u.opcode ++ rest) rows
 simp only [TM2.Reaches,List.append_assoc] at hpre hr
 have h := RejectTrace.prepend hpre hr
 simpa [RejectTrace,u.emitted,payloadBits,List.flatMap_append,List.append_assoc] using h

theorem BinaryContract.second_reject {c p q e₁ e₂} (u : BinaryContract c p q e₁ e₂)
 (r₁ : Row) (hp : Runs p r₁) (hq : Rejects q) : Rejects c := by
 intro s v rest rows
 have hpre := u.prefix_runs s v (payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits u.opcode ++ rest) rows
 have hr := hp (u.operands ++ s) none (payloadBits (TokenVM.emitCert q) ++ tokenBits u.opcode ++ rest) rows
 have hq' := hq (u.operands ++ s) none (tokenBits u.opcode ++ rest) (FramedRow.encode r₁ ++ rows)
 simp only [TM2.Reaches,List.append_assoc] at hpre hr
 have h := RejectTrace.prepend hpre (RejectTrace.prepend hr hq')
 simpa [RejectTrace,u.emitted,payloadBits,List.flatMap_append,List.append_assoc] using h

theorem BinaryContract.wrong_rows {c p q e₁ e₂} (u : BinaryContract c p q e₁ e₂)
 (r₁ r₂ : Row) (hp : Runs p r₁) (hq : Runs q r₂)
 (hne : ¬(e₂ = r₂ ∧ e₁ = r₁)) : Rejects c := by
 intro s v rest rows
 have hpre := u.prefix_runs s v (payloadBits (TokenVM.emitCert p) ++ payloadBits (TokenVM.emitCert q) ++ tokenBits u.opcode ++ rest) rows
 have hr := hp (u.operands ++ s) none (payloadBits (TokenVM.emitCert q) ++ tokenBits u.opcode ++ rest) rows
 have hq' := hq (u.operands ++ s) none (tokenBits u.opcode ++ rest) (FramedRow.encode r₁ ++ rows)
 have hf := u.mismatch r₁ r₂ hne none rest rows s
 simp only [TM2.Reaches,List.append_assoc] at hpre hr hq' hf
 have h := RejectTrace.prepend hpre (RejectTrace.prepend hr (RejectTrace.prepend hq' hf))
 simpa [RejectTrace,u.emitted,payloadBits,List.flatMap_append,List.append_assoc] using h

theorem binary_evaluates {c p q : Executable.Cert} {e₁ e₂ result : Row}
 (u : BinaryContract c p q e₁ e₂) (build : ND e₁ → ND e₂ → ND result)
 (hcheck : Executable.check c = do
   let hp ← Executable.demand (Executable.check p) e₁
   let hq ← Executable.demand (Executable.check q) e₂
   pure ⟨result,build hp.down hq.down⟩)
 (success : Runs p e₁ → Runs q e₂ → Runs c result)
 (hp : Evaluates p) (hq : Evaluates q) : Evaluates c := by
 cases hc : Executable.check p with
 | none =>
   have hr : Rejects p := by simpa [Evaluates,hc] using hp
   simpa [Evaluates,hcheck,Executable.demand,hc] using u.first_reject hr
 | some r₁ =>
   have hr : Runs p r₁.val := by simpa [Evaluates,hc] using hp
   cases hd : Executable.check q with
   | none =>
     have hqr : Rejects q := by simpa [Evaluates,hd] using hq
     have hh := u.second_reject r₁.val hr hqr
     by_cases he : r₁.val = e₁ <;>
       simpa [Evaluates,hcheck,Executable.demand,hc,hd,he] using hh
   | some r₂ =>
     have hqr : Runs q r₂.val := by simpa [Evaluates,hd] using hq
     by_cases he : r₁.val = e₁
     · by_cases hf : r₂.val = e₂
       · have hh := success (he ▸ hr) (hf ▸ hqr)
         simpa [Evaluates,hcheck,Executable.demand,hc,hd,he,hf] using hh
       · have hh := u.wrong_rows r₁.val r₂.val hr hqr (by intro h; exact hf h.1.symm)
         simpa [Evaluates,hcheck,Executable.demand,hc,hd,he,hf] using hh
     · have hh := u.wrong_rows r₁.val r₂.val hr hqr (by intro h; exact he h.2.symm)
       simpa [Evaluates,hcheck,Executable.demand,hc,hd,he] using hh

end RosserDirect.ProofInterpreter
