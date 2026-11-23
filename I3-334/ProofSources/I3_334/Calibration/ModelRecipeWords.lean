module
public import I3_334.Calibration.ModelRecipe
public import I3_334.Calibration.ModelRewrite
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open ArithmeticMachine.SourceWords
open ArithmeticMachine.SourceCantor
open Templates (Instruction Pattern)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The prescribed front effects of a successful row, with no
interpretation of the scheduler's control registers. -/
inductive Fits (values : M) : List Instruction → M × M → M × M → Prop
  | nil (ends : M × M) : Fits values [] ends ends
  | literal (token : Token) {left right : M} {ends : M × M} {rest : List Instruction}
      (after : Fits values rest (left,right) ends) :
      Fits values (.literal token :: rest) (ArithmeticMachine.SourceWords.cons (token.arity : M) (token.tag : M) left,right) ends
  | capture (slot : Fin 4) {left right : M} {ends : M × M} {rest : List Instruction}
      (after : Fits values rest (left,right) ends) :
      Fits values (.capture slot :: rest) (emitVector values.[(slot.val : M)] left,right) ends
  | reverse {left right : M} {ends : M × M} {rest : List Instruction}
      (after : Fits values rest (right,left) ends) :
      Fits values (.reverse :: rest) (left,right) ends

theorem modelTemplate_fit (values : M) (p : Pattern) {rest : List Instruction}
    {left right : M} {ends : M × M} (fit : Fits values rest (left,right) ends) :
    Fits values (p.instructions ++ rest) (emitVector (modelTemplate values p) left,right) ends := by
  induction p generalizing rest left right with
  | capture slot => exact .capture slot fit
  | constant tag =>
    simpa [Pattern.instructions,modelTemplate,modelApplication,joinVectors] using
      (Fits.literal ⟨0,tag⟩ fit)
  | unary tag child ih =>
    have next := Fits.literal ⟨1,tag⟩ (ih fit)
    simpa [Pattern.instructions,modelTemplate,modelApplication,joinVectors] using next
  | binary tag l r ih₁ ih₂ =>
    have next := Fits.literal ⟨2,tag⟩ (ih₁ (ih₂ fit))
    simpa only [Pattern.instructions,modelTemplate,modelApplication,joinVectors,emitVector_cons,
      emitVector_append,appendVector_empty_suffix,List.cons_append,List.append_assoc,Arithmetic.pi₁_pair,
      Arithmetic.pi₂_pair,List.length_cons,List.length_nil,Nat.zero_add,Nat.reduceAdd,Nat.cast_ofNat] using next

noncomputable def modelSelectors (steps : List RecipeStep) (tail : M) : M :=
  match steps with
  | [] => tail
  | .selector k :: rest => pairValue (k : M) (modelSelectors rest tail)
  | _ :: rest => modelSelectors rest tail

def dictTail (value : Nat) (slot : Fin 4) : Nat := if slot = 0 then value else 0

noncomputable def chosenDictionary (value : Nat) (values : M) : M :=
  modelDictionary (fun slot => emitRaw values.[(slot.val : M)] (dictTail value slot : M) (bias slot : M))

theorem modelSlot_safe {values : M} (closed : ModelSubstitution values) (slot : Fin 4) :
    ClosedVector (bias slot : M) values.[(slot.val : M)] := by
  have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · simpa [bias] using closed.2.1
  · change ClosedVector ((0 : Nat) : M) values.[((1 : Nat) : M)]
    simpa only [Nat.cast_zero,Nat.cast_one] using closed.2.2.1
  · change ClosedVector ((0 : Nat) : M) values.[((2 : Nat) : M)]
    simpa only [Nat.cast_zero,Nat.cast_ofNat] using closed.2.2.2.1
  · change ClosedVector ((3 : Nat) : M) values.[((3 : Nat) : M)]
    simpa only [Nat.cast_ofNat] using closed.2.2.2.2

structure RecipeState (s : Store M) (n p mark dict : M) : Prop where
  scratch : Scratch s
  index : s np = n
  pending : s pl = p
  marker : s gues = mark
  dictionary : s dc = dict
  counter : s goal = 0
  unused : s 11 = 0

theorem RecipeState.selector {s : Store M} {n p mark dict q : M}
    (ready : RecipeState s n p mark dict) :
    RecipeState (s.set pl q) n q mark dict := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [Scratch.iff_fields,Store.set,pl,expected,tok,u] using Scratch.iff_fields.mp ready.scratch
  all_goals
    simp [Store.set,np,pl,gues,dc,goal,ready.index,ready.marker,ready.dictionary,ready.counter,ready.unused]

theorem RecipeState.tail {s : Store M} {n p mark dict : M}
    (ready : RecipeState s n p mark dict) :
    RecipeState (s.set tmp 0) n p mark dict := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [Scratch.iff_fields,Store.set,tmp,expected,tok,u] using Scratch.iff_fields.mp ready.scratch
  all_goals
    simp [Store.set,np,pl,gues,dc,goal,tmp,ready.index,ready.pending,ready.marker,
      ready.dictionary,ready.counter,ready.unused]

theorem coded_fit_step {values : M} (closed : ModelSubstitution values) (value : Nat)
    {i : Instruction} {rest : List Instruction} {s : Store M} {ends : M × M} {n p mark : M}
    (fit : Fits values (i :: rest) (s fr,s lv) ends)
    (ready : RecipeState s n p mark (chosenDictionary value values)) :
    ∃ t, RecipeTransition (.emit i) s t ∧
      Fits values rest (t fr,t lv) ends ∧ RecipeState t n p mark (chosenDictionary value values) ∧
      ∀ slot, i = .capture slot → t tmp = (dictTail value slot : M) := by
  cases i with
  | literal token =>
    generalize h : (s fr,s lv) = first at fit
    cases fit with
    | @literal _ a b _ _ next =>
      rcases Prod.mk.inj h with ⟨left,right⟩
      let t := modelLiteralEffect token s
      have exactFront : t = (s.set fr a).set gues (s gues) := by
        simp only [t,modelLiteralEffect,left,ArithmeticMachine.SourceWords.tail_cons,emitVector_arity, ArithmeticMachine.SourceWords.decodeLeft_cons,ArithmeticMachine.SourceWords.decodeRight_cons,(decode_pairValue _ _).1,and_self,↓reduceIte]
      have clean : Scratch t := by
        simpa [Scratch.iff_fields,exactFront,Store.set,fr, gues,expected,tok,u] using Scratch.iff_fields.mp ready.scratch
      have state : RecipeState t n p mark (chosenDictionary value values) := by
        refine ⟨clean,?_,?_,?_,?_,?_,?_⟩ <;>
          simp [exactFront,Store.set,np,pl,gues,dc,goal,fr,ready.index,ready.pending,ready.marker,
            ready.dictionary,ready.counter,ready.unused]
      refine ⟨t,.emit (coded_literalToken token s ready.scratch) clean,?_,state,by simp⟩
      simpa [exactFront,Store.set,gues,fr,lv,right] using next
  | capture slot =>
    generalize h : (s fr,s lv) = first at fit
    cases fit with
    | @capture _ a b _ _ next =>
      rcases Prod.mk.inj h with ⟨left,right⟩
      let t := modelScanner s 0 (dictTail value slot : M) a
      have clean := modelScanner_clean s ready.scratch 0 (dictTail value slot : M) a
      have run := coded_scan_selected slot s ready.scratch _ _ _
        (by rw [ready.dictionary,chosenDictionary,modelSlot_dictionary]) left (modelSlot_safe closed slot)
      have state : RecipeState t n p mark (chosenDictionary value values) := by
        refine ⟨clean,?_,?_,?_,?_,?_,?_⟩ <;>
          simp [t,modelScanner,Store.set,np,pl,gues,dc,goal,fr,tmp,ready.index,ready.pending,ready.marker,
            ready.dictionary,ready.unused]
      refine ⟨t,.emit run clean,?_,state,?_⟩
      · simpa [t,modelScanner,Store.set,goal,tmp,fr,lv,right] using next
      · intro other same
        injection same with same
        subst other
        simp [t,modelScanner,Store.set,fr,tmp]
  | reverse =>
    generalize h : (s fr,s lv) = first at fit
    cases fit with
    | reverse next =>
      rcases Prod.mk.inj h with ⟨left,right⟩
      let t := (s.set fr (s lv)).set lv (s fr)
      have clean : Scratch t := by
        simpa [Scratch.iff_fields,t,Store.set,fr,lv,expected,tok,u] using Scratch.iff_fields.mp ready.scratch
      have state : RecipeState t n p mark (chosenDictionary value values) := by
        refine ⟨clean,?_,?_,?_,?_,?_,?_⟩ <;>
          simp [t,Store.set,np,pl,gues,dc,goal,fr,lv,ready.index,ready.pending,ready.marker,
            ready.dictionary,ready.counter,ready.unused]
      refine ⟨t,.emit (coded_exchange s ready.scratch.auxiliaryEmpty) clean,?_,state,by simp⟩
      simpa [t,Store.set,fr,lv,left,right] using next

theorem coded_recipe_words {values : M} (closed : ModelSubstitution values) (steps : List RecipeStep)
    (value : Nat) (tail : M) (valid : validRecipe value steps = true)
    {s : Store M} {ends : M × M} {n mark : M}
    (fit : Fits values (emitted steps) (s fr,s lv) ends)
    (ready : RecipeState s n (modelSelectors steps tail) mark (chosenDictionary value values)) :
    ∃ t, RecipeTrace steps s t ∧ (t fr,t lv) = ends ∧
      RecipeState t n tail mark (chosenDictionary value values) := by
  induction steps using List.twoStepInduction generalizing s with
  | nil =>
    cases fit
    exact ⟨s,.nil _,rfl,ready⟩
  | singleton a =>
    cases a with
    | tail k => simp [validRecipe] at valid
    | selector k =>
      have word : s pl = pairValue (k : M) tail := ready.pending
      have left : decodeLeft (s pl) = (k : M) := by rw [word, (decode_pairValue _ _).1]
      have right : decodeRight (s pl) = tail := by rw [word, (decode_pairValue _ _).2]
      refine ⟨s.set pl (decodeRight (s pl)),.cons (.selector ready.counter left) (.nil _),?_,?_⟩
      · cases fit
        simp [Store.set,fr,lv,pl]
      · rw [right]
        exact ready.selector
    | emit i =>
      obtain ⟨t,op,after,state,_⟩ := coded_fit_step closed value fit ready
      cases after
      exact ⟨t,.cons op (.nil _),rfl,state⟩
  | cons_cons a b rest head tailIH =>
    cases a with
    | tail k => simp [validRecipe] at valid
    | selector k =>
      have word : s pl = pairValue (k : M) (modelSelectors (b::rest) tail) := ready.pending
      have left : decodeLeft (s pl) = (k : M) := by rw [word, (decode_pairValue _ _).1]
      have right : decodeRight (s pl) = modelSelectors (b::rest) tail := by rw [word, (decode_pairValue _ _).2]
      let mid := s.set pl (decodeRight (s pl))
      have now : RecipeState mid n (modelSelectors (b::rest) tail) mark (chosenDictionary value values) := by
        rw [← right]
        exact ready.selector
      have remaining : Fits values (emitted (b::rest)) (mid fr,mid lv) ends := by
        simpa [emitted,mid,Store.set,fr,lv,pl] using fit
      obtain ⟨t,trace,done,state⟩ := tailIH b (by simpa only [validRecipe] using valid) remaining now
      exact ⟨t,.cons (.selector ready.counter left) trace,done,state⟩
    | emit i =>
      obtain ⟨mid,op,after,state,temp⟩ := coded_fit_step closed value fit ready
      by_cases suffix : ∃ slot k, i = .capture slot ∧ b = .tail k
      · obtain ⟨slot,k,rfl,rfl⟩ := suffix
        have ok := valid
        simp only [validRecipe,Bool.and_eq_true,beq_iff_eq] at ok
        obtain ⟨⟨rfl,rfl⟩,good⟩ := ok
        have tempEq := temp 0 rfl
        simp only [dictTail,↓reduceIte] at tempEq
        have clean := state.tail
        have remaining : Fits values (emitted rest) ((mid.set tmp 0) fr,(mid.set tmp 0) lv) ends := by
          simpa [emitted,Store.set,tmp,fr,lv] using after
        obtain ⟨t,trace,done,finish⟩ := head good remaining clean
        exact ⟨t,.cons op (.cons (.tail tempEq) trace),done,finish⟩
      · have validTail : validRecipe value (b::rest) = true := by
          cases i <;> cases b <;> simp_all [validRecipe]
        obtain ⟨t,trace,done,finish⟩ := tailIH b validTail after state
        exact ⟨t,.cons op trace,done,finish⟩

end PalomarI3334.SearchProgram
