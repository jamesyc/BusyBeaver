module
public import ModelFiniteMacroHistory
public import ModelResidualTail
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.ModelCommands
open ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def exhausted (code:M) : Prop := ∃s:Store M,code=commandCfgCode 0 s
noncomputable def cfgFormula : ArithmeticSemiformula Nat 6 :=
 “z pc t w d h. ∃s, !storeGraph s t w d h ∧ !exactCantorGraph z pc s”
lemma cfgFormula_eval (ρ:Nat→M) (z pc t w d h:M) :
 cfgFormula.Eval ![z,pc,t,w,d,h] ρ ↔ z=commandCfgCode pc ⟨t,w,d,h⟩ := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [cfgFormula,commandCfgCode,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,hc,storeGraph_eval]
noncomputable def exhaustedFormula : ArithmeticSemiformula Nat 1 :=
 “z. ∃t, ∃w, ∃d, ∃h, !cfgFormula z 0 t w d h”
lemma exhaustedFormula_eval (ρ:Nat→M) (z:M) : exhaustedFormula.Eval ![z] ρ ↔ exhausted z := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [exhaustedFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',hv,cfgFormula_eval]
 constructor
 · rintro ⟨t,w,d,h,he⟩; exact ⟨⟨t,w,d,h⟩,he⟩
 · rintro ⟨⟨t,w,d,h⟩,he⟩; exact ⟨t,w,d,h,he⟩
def terminalFrom (pc:M) : Prop := ∀(s:Store M) (initial hist:M),
 runHistory initial hist → modelListHead hist=commandCfgCode pc s →
 ∃out:M,runHistory initial out ∧ (haltAt (modelListHead out) ∨ exhausted (modelListHead out))
noncomputable def terminalFromFormula : ArithmeticSemiformula Nat 1 :=
 “pc. ∀t, ∀w, ∀d, ∀h, ∀initial, ∀hist, ∀head,
 (!runFormula initial hist ∧ !listHeadGraph head hist ∧ !cfgFormula head pc t w d h) →
 ∃out, ∃last, !runFormula initial out ∧ !listHeadGraph last out ∧ (!haltFormula last ∨ !exhaustedFormula last)”
lemma terminalFromFormula_eval (ρ:Nat→M) (pc:M) :
 terminalFromFormula.Eval ![pc] ρ ↔ terminalFrom pc := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [terminalFromFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,
 runFormula_eval,ruleHead_defined.iff,cfgFormula_eval,haltFormula_eval,exhaustedFormula_eval]
 constructor
 · intro h s initial hist hr hh
   exact h s.t s.w s.d s.h initial hist hr (by cases s; exact hh)
 · intro h t w d hh initial hist hr he
   exact h ⟨t,w,d,hh⟩ initial hist hr he
noncomputable def terminalFrom_certificate (ρ:Nat→M) :
 FormulaCertificate ρ 1 (fun v=>terminalFrom (v 0)) := by
 refine ⟨terminalFromFormula,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (terminalFromFormula_eval ρ (v 0)).symm
/-- Every internally coded residual command word finishes or reaches an actual
failed SHIFT, from any given rooted prefix. Genuine first-order PA induction. -/
theorem command_totality : ∀pc:M,terminalFrom pc := by
 apply (terminalFrom_certificate (fun _=>0)).orderInduction
 intro pc ih
 change terminalFrom pc
 intro s initial hist hr hh
 by_cases hz:pc=0
 · exact ⟨hist,hr,Or.inr ⟨s,by simpa [hz] using hh⟩⟩
 · have hp:0<pc := pos_iff_ne_zero.mpr hz
   let parsed:=parseCommand (modelPredecessor pc)
   have he:commandCode parsed.1 parsed.2+1=pc := by
    rw [show commandCode parsed.1 parsed.2=modelPredecessor pc from commandCode_parse _]
    exact modelPredecessor_of_pos pc hp
   have ht:parsed.2<pc := by rw [←he]; exact command_residual_descends _ _
   cases hc:modelCommandEval parsed.1 s with
   | none =>
     refine ⟨hist,hr,Or.inl ?_⟩
     rw [hh,←he]
     exact command_failure_halt _ _ _ hc
   | some out =>
     have hs:codedCommandStep (modelListHead hist) (commandCfgCode parsed.2 out) := by
      rw [hh,←he]; exact codedCommandStep_of_eval _ _ _ _ hc
     exact ih parsed.2 ht out initial _ (runHistory_extend hr hs) (modelListHead_cons _ _)
end ZF209.ModelCommands
