module
public import ModelRuntimeEncoding
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation M6.Runtime
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma model_box_mark (pre post:List M) (v spares l:M) (hr:pre.length<9) :
 Reaches (namedState (sk pre.length) l (modelBox (pre++v::post) spares (.plain .none) 0))
 (namedLeft (markExit pre.length) l (modelBox (pre++v::post) spares (.mark pre.length) 0)) := by
 simpa only [modelBox,List.foldr_append,List.foldr_cons,markedFile_split] using
  native_mark_primary pre v l (post.foldr registerBlock (spareRun spares 0)) hr
lemma model_box_increment (pre post:List M) (v spares l:M) :
 Reaches (namedState 64 l (modelBox (pre++v::post) spares (.mark pre.length) 0))
 (namedLeft 40 l (modelBox (pre++v::post) spares (.plain (.inc pre.length)) 0)) := by
 simpa only [modelBox,markedFile_split,primaryIncrement_split,List.foldr_append,List.foldr_cons] using
  native_increment_file pre post v spares l
lemma model_box_decrement_positive (pre post:List M) (v spares l:M) :
 Reaches (namedState 0 l (modelBox (pre++(v+1)::post) spares (.mark pre.length) 0))
 (namedLeft 40 (1+2*l) (modelBox (pre++(v+1)::post) spares (.plain (.dec pre.length)) 0)) := by
 simpa only [modelBox,markedFile_split,primaryDecrement_split,modelPredecessor_succ,List.foldr_append,List.foldr_cons] using
  native_decrement_positive_file pre post v spares l
lemma model_box_decrement_zero (pre post:List M) (spares l:M) :
 Reaches (namedState 0 l (modelBox (pre++0::post) (spares+1) (.mark pre.length) 0))
 (namedLeft 97 l (modelBox (pre++0::post) (spares+1) (.plain .none) 0)) := by
 simpa only [modelBox,markedFile_split,List.foldr_append,List.foldr_cons] using
  native_decrement_zero_file pre post spares l
end ZF209.BinaryTape
