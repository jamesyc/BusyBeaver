module
public import I3_334.Calibration.ModelRecipeWords
public import I3_334.Calibration.ModelScheduler
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (CodedLines ifZero)
open ArithmeticMachine.SourceCantor
open ArithmeticMachine.SourceWords
open Templates (Equation equationInstructions)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelInput (proposal context dictionary selectors : M) : M :=
  pairValue proposal (pairValue context (pairValue dictionary selectors))

noncomputable def modelTrieInput (s : Scheduler M) (proposal left right dictionary selectors : M) : Store M :=
  (((((s.store.set pl selectors).set fr left).set lv right).set dc dictionary).set gues proposal)

theorem coded_input_exact (s : Scheduler M) (proposal left right dictionary selectors prefixWord : M) (rev : Bool)
    (input : s.begin.pending = modelInput proposal (2*len prefixWord+(rev.toNat : M)) dictionary selectors)
    (before : s.begin.incumbent = emitVector prefixWord left)
    (after : proposal = emitVector prefixWord right) :
    CodedLines [ifZero pl restart,produce,read goal,contextScan,read dc] s.store.code
      (modelTrieInput s.begin proposal (if rev then right else left) (if rev then left else right)
        dictionary selectors).code := by
  let B := s.begin
  let context := 2*len prefixWord+(rev.toNat : M)
  let first := ((B.store.set pl (pairValue context (pairValue dictionary selectors))).set gues proposal).set lv proposal
  have produce : SearchProgram.produce.Runs .normal B.store.code first.code := by
    have run := coded_produce B.store (modelScratch B)
      (by simp [B,Scheduler.store,Store.set,np,pl,fr,tmp,gues])
      (by simp [B,Scheduler.store,Store.set,np,pl,fr,tmp,lv])
    simpa [first,modelProduce,B,Scheduler.store,Store.set,np,pl,fr,tmp,input,modelInput,context,decode_pairValue]
      using run
  let loaded := (first.set pl (pairValue dictionary selectors)).set goal context
  have cleanFirst : Scratch first := by
    simpa [Scratch.iff_fields, first,Store.set,pl,gues,lv,expected,tok,u] using
      Scratch.iff_fields.mp (modelScratch B)
  have load : (read goal).Runs .normal first.code loaded.code := by
    have run := coded_read (dst := goal) (by decide) (by decide) first cleanFirst.tokenEmpty cleanFirst.auxiliaryEmpty
    simpa [loaded,first,Store.set,np,pl,fr,tmp,gues,lv,goal,Scheduler.store,decode_pairValue] using run
  have cleanLoaded : Scratch loaded := by
    simpa [Scratch.iff_fields,loaded,Store.set,pl,goal,expected,tok,u] using Scratch.iff_fields.mp cleanFirst
  let a := if rev then right else left
  let b := if rev then left else right
  let matched := contextState loaded 0 a b proposal
  have contextRun : contextScan.Runs .normal loaded.code matched.code := by
    have check : loaded goal = 2*len prefixWord+(rev.toNat : M) := Store.get_set ..
    have leftWord : loaded fr = emitVector prefixWord left := by
      simpa [loaded,first,Store.set,np,pl,fr,tmp,gues,lv,goal,Scheduler.store,B] using before
    have rightWord : loaded lv = emitVector prefixWord right := by
      simpa [loaded,first,Store.set,pl,goal,lv] using after
    have mark : loaded gues = proposal := by simp [loaded,first,Store.set,pl,goal,lv,gues]
    simpa only [matched,a,b,mark] using coded_context_shared loaded cleanLoaded prefixWord left right rev check leftWord rightWord
  have cleanMatched := (model_context_front loaded a b proposal cleanLoaded).scratch
  have loadDict := coded_read (dst := dc) (by decide) (by decide) matched cleanMatched.tokenEmpty cleanMatched.auxiliaryEmpty
  have exactStore : ((matched.set pl (decodeRight (matched pl))).set dc
      (matched dc+decodeLeft (matched pl))) = modelTrieInput B proposal a b dictionary selectors := by
    apply Source.store_ext <;>
      simp [matched,contextState,replaceFronts,loaded,first,modelTrieInput,Scheduler.store,Store.set,
        np,pl,fr,tmp,gues,lv,goal,dc,expected,tok,u,decode_pairValue]
  rw [exactStore] at loadDict
  exact .cons (coded_begin s) (.cons produce (.cons load (.cons contextRun (.cons loadDict (.nil _)))))

theorem modelRewrite_coded_trial {x y : M} (step : ModelRewrite x y) (tail : M) :
    ∃ input > 0, ∀ s : Scheduler M, s.begin.pending = input → s.begin.incumbent = emitVector x 0 →
      ∃ scratchWord, main.Runs (trialFlow (emitVector y 0)) s.store.code
        (s.finish tail (emitVector y 0) scratchWord).store.code := by
  obtain ⟨eq,listed,values,prefixWord,rest,valid,shape⟩ := step
  have eqRow : equationInstructions eq ∈ templateTable := List.mem_map.mpr ⟨_,listed,rfl⟩
  let actions := rowRecipe (equationInstructions eq)
  obtain ⟨plan,emits,recipeValid⟩ := rowRecipe_ok _ eqRow
  let suffixChoice := tailChoice actions
  let dict := chosenDictionary suffixChoice values
  let selectors := modelSelectors actions tail
  let proposal := emitVector y 0
  let suffix := emitVector rest 0
  let l := emitVector (modelTemplate values eq.1) suffix
  let r := emitVector (modelTemplate values eq.2) suffix
  have matched : Fits values (emitted actions) (l,r) (suffix,suffix) := by
    rw [show emitted actions = equationInstructions eq from emits, equationInstructions]
    have right : Fits values eq.2.instructions (r,suffix) (suffix,suffix) := by
      simpa only [List.append_nil,r] using modelTemplate_fit values eq.2 (Fits.nil (suffix,suffix))
    exact modelTemplate_fit values eq.1 (.reverse right)
  have orient : ∃ rev : Bool, emitVector x 0 = emitVector prefixWord (if rev then r else l) ∧
      proposal = emitVector prefixWord (if rev then l else r) := by
    simp only [modelMatch] at shape
    rcases shape with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact ⟨false,by simp [hx,modelMatch,contextWord,l,r,suffix,emitVector_append],
        by simp [proposal,hy,modelMatch,contextWord,l,r,suffix,emitVector_append]⟩
    · exact ⟨true,by simp [hx,modelMatch,contextWord,l,r,suffix,emitVector_append],
        by simp [proposal,hy,modelMatch,contextWord,l,r,suffix,emitVector_append]⟩
  obtain ⟨rev,oldWord,newWord⟩ := orient
  let input := modelInput proposal (2*len prefixWord+(rev.toNat : M)) dict selectors
  have nonnil : y ≠ 0 := by
    have nonempty (p : Templates.Pattern) : modelTemplate values p ≠ 0 := by
      cases p with
      | capture slot =>
        have guard := modelSlot_safe valid slot
        intro empty
        change values.[(slot.val : M)] = 0 at empty
        rw [empty] at guard
        obtain ⟨trace,length,left,right,_⟩ := guard
        rw [len_nil] at right
        have impossible : (1 : M) = 0 := by simpa using congrArg (fun z : M => π₂ z) (left.symm.trans right)
        exact Arithmetic.one_ne_zero impossible
      | constant tag => simp [modelTemplate,modelApplication]
      | unary tag arg => simp [modelTemplate,modelApplication]
      | binary tag a b => simp [modelTemplate,modelApplication]
    have body (p : Templates.Pattern) : contextWord prefixWord (modelTemplate values p) rest ≠ 0 := by
      intro empty
      have lengths := congrArg len empty
      simp only [contextWord,appendVector_length,len_nil] at lengths
      have positive : 0 < len (modelTemplate values p) :=
        lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm (fun h => nonempty p (len_zero_iff_eq_nil.mp h)))
      have grows : len (modelTemplate values p) ≤ len prefixWord + (len (modelTemplate values p) + len rest) :=
        (le_add_of_nonneg_right (Arithmetic.zero_le _)).trans (le_add_of_nonneg_left (Arithmetic.zero_le _))
      exact (not_lt_of_ge (le_of_eq lengths)) (positive.trans_le grows)
    simp only [modelMatch] at shape
    rcases shape with ⟨_,hy⟩ | ⟨_,hy⟩
    · rw [hy]; exact body eq.2
    · rw [hy]; exact body eq.1
  have positive : 0 < input := (emitVector_nonempty nonnil _).trans_le (by
    simpa [input,modelInput,(decode_pairValue _ _).1] using (decodeValue_bounds input).1)
  refine ⟨input,positive,?_⟩
  intro s ready current
  let start := modelTrieInput s.begin proposal l r dict selectors
  have first := coded_input_exact s proposal (if rev then r else l) (if rev then l else r) dict selectors prefixWord rev
    ready (current.trans oldWord) newWord
  have setup : CodedLines [ifZero pl restart,produce,read goal,contextScan,read dc] s.store.code start.code := by
    cases rev <;> simpa only [Bool.false_eq_true,↓reduceIte,start] using first
  have state : RecipeState start s.begin.index selectors proposal dict := by
    refine ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_,?_,?_⟩ <;>
      simp [start,modelTrieInput,Scheduler.store,Store.set,np,pl,fr,lv,goal,dc,gues,tmp,tok,expected,u]
  have fronts : Fits values (emitted actions) (start fr,start lv) (suffix,suffix) := by
    simpa [start,modelTrieInput,Store.set,gues,dc,fr,lv] using matched
  obtain ⟨final,replay,out,endState⟩ := coded_recipe_words valid actions suffixChoice tail recipeValid fronts state
  have row : CodedLines rows start.code final.code := coded_recipe templateFuel templateTable _ plan state.scratch replay
  have executed := coded_trial s setup row endState.scratch endState.unused endState.index
  have marker : finalMark final = proposal := by
    have equal : final fr = final lv := (congrArg Prod.fst out).trans (congrArg Prod.snd out).symm
    simp [finalMark,markedIf,equal,endState.marker]
  rw [marker,endState.pending] at executed
  exact ⟨final tmp,executed⟩

end PalomarI3334.SearchProgram
