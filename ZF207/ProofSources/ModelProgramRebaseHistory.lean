module
public import ModelProgramRebase
public import ModelMapGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def rebaseHistory (code tail:M) : M :=
 ModelOperationalConcat.map rebaseCfgGraph rebaseCfg rebaseCfg_defined code tail
lemma rebaseHistory_head {code:M} (tail:M) (h:code≠0) :
 modelListHead (rebaseHistory code tail)=rebaseCfg (modelListHead code) tail :=
 ModelOperationalConcat.map_head _ _ _ tail h
lemma rebaseHistory_halt {code:M} (tail:M) (hn:code≠0) (h:haltAt (modelListHead code)) :
 haltAt (modelListHead (rebaseHistory code tail)) := by
 rw [rebaseHistory_head tail hn]
 exact rebaseCfg_halt tail h
lemma rebaseHistory_exhausted {code:M} (tail:M) (s:Store M) (hn:code≠0)
 (h:modelListHead code=commandCfgCode 0 s) :
 modelListHead (rebaseHistory code tail)=commandCfgCode tail s := by
 rw [rebaseHistory_head tail hn,h,rebaseCfg_exhausted]
end ZF207.ModelCommands
