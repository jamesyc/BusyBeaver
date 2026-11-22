module
public import ZF192Support.Execution.Commands.Program.AppendGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Splice a continuation into the residual program pointer; preserve packed store literally. -/
noncomputable def rebaseCfg (code tail:M) : M :=
 modelCantor (programAppend (modelUnpairLeft code) tail) (modelUnpairRight code)
lemma rebaseCfg_cfg (pointer:M) (s:Store M) (tail:M) :
 rebaseCfg (commandCfgCode pointer s) tail=commandCfgCode (programAppend pointer tail) s := by
 simp only [rebaseCfg,commandCfgCode,modelUnpairLeft_pair,modelUnpairRight_pair]
lemma rebaseCfg_exhausted (s:Store M) (tail:M) : rebaseCfg (commandCfgCode 0 s) tail=commandCfgCode tail s := by
 rw [rebaseCfg_cfg,programAppend_zero]
lemma rebaseCfg_step (tail:M) {before after:M} (h:codedCommandStep before after) :
 codedCommandStep (rebaseCfg before tail) (rebaseCfg after tail) := by
 rcases h with ⟨c,next,s,s',rfl,rfl,he⟩
 rw [rebaseCfg_cfg,rebaseCfg_cfg,programAppend_cons]
 exact codedCommandStep_of_eval c (programAppend next tail) s s' he
lemma rebaseCfg_halt (tail:M) {code:M} (h:haltAt code) : haltAt (rebaseCfg code tail) := by
 rcases h with ⟨next,s,rfl,hh⟩
 rw [rebaseCfg_cfg,programAppend_cons]
 exact ⟨programAppend next tail,s,rfl,hh⟩
def rebaseCfgGraphOf (app : 𝚺ᴬ₁.Semisentence 3) : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z code tail. ∃p, ∃s, ∃q, !unpairLeftGraph p code ∧ !unpairRightGraph s code ∧
 !app q p tail ∧ !exactCantorGraph z q s”
def rebaseCfgGraph : 𝚺ᴬ₁.Semisentence 3 := rebaseCfgGraphOf programAppendGraph
lemma rebaseCfgGraphOf_eval (app : 𝚺ᴬ₁.Semisentence 3) (f:M→M→M)
 (hf:𝚺ᴬ₁.DefinedFunction₂ f app) (v:Fin 3→M) :
 (rebaseCfgGraphOf app).val.Evalb v ↔
 v 0=modelCantor (f (modelUnpairLeft (v 1)) (v 2)) (modelUnpairRight (v 1)) := by
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b :=
  graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 have hl (z n:M) : unpairLeftGraph.val.Evalb ![z,n] ↔ z=modelUnpairLeft n :=
  graphValue_spec unpairLeftGraph unpairLeftGraph_total z ![n]
 have hr (z n:M) : unpairRightGraph.val.Evalb ![z,n] ↔ z=modelUnpairRight n :=
  graphValue_spec unpairRightGraph unpairRightGraph_total z ![n]
 simp [rebaseCfgGraphOf,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,
 Empty.eq_elim,Matrix.constant_eq_singleton,hc,hl,hr,hf.iff]
lemma rebaseCfg_defined : 𝚺ᴬ₁.DefinedFunction₂ (rebaseCfg (M:=M)) rebaseCfgGraph := .mk (by
 intro v; exact rebaseCfgGraphOf_eval _ _ programAppend_defined v)
instance rebaseCfg_definable : 𝚺ᴬ₁-Function₂ (rebaseCfg (M:=M)) := rebaseCfg_defined.to_definable
end ZF192Support.ModelCommands
