module
public import ModelCommandRun
public import ModelCTraceInduction
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def cleanCfg (pc t w:M) : M := commandCfgCode pc ⟨t,w,0,0⟩
noncomputable def cleanCfgFormula : ArithmeticSemiformula Nat 4 :=
 “z pc t w. ∃s, !storeGraph s t w 0 0 ∧ !exactCantorGraph z pc s”
lemma cleanCfgFormula_eval (ρ:Nat→M) (z pc t w:M) :
 cleanCfgFormula.Eval ![z,pc,t,w] ρ ↔ z=cleanCfg pc t w := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [hv,cleanCfgFormula,cleanCfg,commandCfgCode,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Empty.eq_elim,hc,storeGraph_eval]
/-- The word is an internal live/exhausted residual pointer. Histories may be
nonstandard in length; all initial top/store values are quantified in the model. -/
def compilable (n:M) : Prop := ∃word:M,∀t w:M,∃hist:M,
 runHistory (cleanCfg word t w) hist ∧
 (haltAt (modelListHead hist) ∨ modelListHead hist=cleanCfg 0 n w)
noncomputable def compilableFormula : ArithmeticSemiformula Nat 1 :=
 “n. ∃word, ∀t, ∀w, ∃hist, ∃initial, ∃last, ∃result,
 !cleanCfgFormula initial word t w ∧ !cleanCfgFormula result 0 n w ∧
 !listHeadGraph last hist ∧ !runFormula initial hist ∧ (!haltFormula last ∨ last=result)”
lemma compilableFormula_eval (ρ:Nat→M) (n:M) :
 compilableFormula.Eval ![n] ρ ↔ compilable n := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [compilableFormula,compilable,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,cleanCfgFormula_eval,
 ruleHead_defined.iff,runFormula_eval,haltFormula_eval]
def compilerInvariant (p:M) : Prop := ∀r:M,modelMember r p → compilable r
noncomputable def compilerInvariantFormula : ArithmeticSemiformula Nat 1 :=
 “p. ∀r, !memberFormula r p → !compilableFormula r”
lemma compilerInvariantFormula_eval (ρ:Nat→M) (p:M) :
 compilerInvariantFormula.Eval ![p] ρ ↔ compilerInvariant p := by
 have hv (z:M) : (fun _ : Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [compilerInvariantFormula,compilerInvariant,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,ruleMember_defined.iff,compilableFormula_eval]
noncomputable def compilerInvariant_certificate (ρ:Nat→M) :
 FormulaCertificate ρ 1 (fun v=>compilerInvariant (v 0)) := by
 refine ⟨compilerInvariantFormula,?_⟩
 intro v
 have hv : v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (compilerInvariantFormula_eval ρ (v 0)).symm
lemma compilerInvariant_zero : compilerInvariant (0:M) := by
 intro r hr
 have hn : ¬ modelMember r (0:M) := by simp [modelMember,modelMemberCode_zero]
 exact False.elim (hn hr)
/-- This gate exposes, rather than assumes silently, the three concrete compiler
closure obligations still needed for uniform internal compilation. -/
theorem compilerInvariant_of_closures
 (ax : ∀n:M,modelCAxiom n → compilable n)
 (mp : ∀a b:M,compilable a → compilable (t299 a b) → compilable b)
 (gen : ∀i a:M,compilable a → compilable (t322 i a)) :
 ∀p:M,modelTrace modelCRule p → compilerInvariant p := by
 apply modelCTrace_induction (fun _=>0) compilerInvariant (compilerInvariant_certificate _) compilerInvariant_zero
 intro a b _ ih ha r hr
 rcases (modelMember_cons r a b).mp hr with he | hm
 · subst r
   rcases ha with ha | hm | hg
   · exact ax a ha
   · obtain ⟨x,hx,himp⟩ := hm
     exact mp x a (ih x hx) (ih _ himp)
   · obtain ⟨i,x,hx,rfl⟩ := hg
     exact gen i x (ih x hx)
 · exact ih r hm
end ZF207.ModelCommands
