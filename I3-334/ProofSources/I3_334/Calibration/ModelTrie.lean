module
public import I3_334.Calibration.ModelInstructions
public import I3_334.Search.TrieSoundness
public import I3_334Support.Search.Arithmetic.ModelDispatch
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (CodedLines block inc dec break_ coded_decrement_zero coded_decrement_positive
  modelSelect modelSelect_exists modelSelect_map)
open ArithmeticMachine.SourceCantor
open ArithmeticMachine.SourceWords (tail)
open Templates (Instruction)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelLiteralEffect (token : Token) (s : Store M) : Store M :=
  (s.set fr (tail (s fr))).set gues
    (if decodeLeft (s fr) = (token.arity : M)+1 ∧
        decodeLeft (decodeRight (s fr)) = (token.tag : M) then s gues else 0)

theorem coded_literalToken (token : Token) (s : Store M) (clean : Scratch s) :
    (literalToken token).Runs .normal s.code (modelLiteralEffect token s).code := by
  let raised := s.set expected ((token.arity : M) + 1)
  let middle := modelConsume raised
  let retag := middle.set expected (token.tag : M)
  have first : CodedLines (List.replicate (token.arity+1) (inc expected)) s.code raised.code := by
    simpa only [raised,clean.expectedEmpty,zero_add,Nat.cast_succ] using
      coded_increments expected (token.arity+1) s
  have check₁ : eat.Runs .normal raised.code middle.code := coded_eat raised
    (by simpa [raised,Store.set,tok,expected] using clean.tokenEmpty)
    (by simpa [raised,Store.set,u,expected] using clean.auxiliaryEmpty)
  have zero : middle expected = 0 := by simp [middle,modelConsume,Store.set,expected,gues]
  have tag : CodedLines (List.replicate token.tag (inc expected)) middle.code retag.code := by
    simpa only [retag,zero,zero_add] using coded_increments expected token.tag middle
  have check₂ : eat.Runs .normal retag.code (modelConsume retag).code := coded_eat retag
    (by simpa [retag,middle,modelConsume,raised,Store.set,tok,expected,fr,gues] using clean.tokenEmpty)
    (by simpa [retag,middle,modelConsume,raised,Store.set,u,expected,fr,gues] using clean.auxiliaryEmpty)
  have result : modelConsume retag = modelLiteralEffect token s := by
    funext i
    by_cases a : i = expected <;> by_cases f : i = fr <;> by_cases g : i = gues <;>
      simp [modelLiteralEffect,tail,modelConsume,retag,middle,raised,Store.set,
        a,f,g,fr,expected,gues,clean.expectedEmpty]
    all_goals
      by_cases ha : (token.arity : M)+1 = decodeLeft (s fr) <;>
      by_cases ht : (token.tag : M) = decodeLeft (decodeRight (s fr)) <;>
        simp [ha,ht,eq_comm]
  rw [result] at check₂
  simpa only [literalToken,List.append_assoc] using
    ((first.append (.cons check₁ (.nil _))).append (tag.append (.cons check₂ (.nil _)))).block

theorem coded_dispatchBy (counter : Register) (ps : List Program) (s : Store M)
    {branch : Program} {r finish : M}
    (selection : modelSelect ps (s counter) = some (branch,r))
    (run : branch.Runs .normal (s.set counter r).code finish) :
    (dispatchBy counter ps).Runs .normal s.code finish := by
  induction ps generalizing s branch r finish with
  | nil => simp [modelSelect] at selection
  | cons first rest ih =>
    cases rest with
    | nil =>
      simp only [modelSelect,Option.some.injEq,Prod.mk.injEq] at selection
      obtain ⟨rfl,rfl⟩ := selection
      simpa only [dispatchBy,Store.set_same] using run
    | cons next ps =>
      by_cases zero : s counter=0
      · simp only [modelSelect,zero,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at selection
        obtain ⟨rfl,rfl⟩ := selection
        have unchanged : s.set counter 0=s := by rw [← zero,Store.set_same]
        rw [unchanged] at run
        exact Program.Runs.rightExit (Program.Runs.leftExit (coded_decrement_zero zero) rfl) run rfl
      · let nextState := s.set counter (s counter-1)
        have selected : modelSelect (next::ps) (nextState counter) = some (branch,r) := by
          simpa only [modelSelect,zero,↓reduceIte,nextState,Store.get_set] using selection
        have child : branch.Runs .normal (nextState.set counter r).code finish := by
          simpa only [nextState,Store.set_set] using run
        have tail := ih nextState selected child
        have canBreak : (break_ 1).Runs (.escape 0) finish finish := ⟨rfl,rfl⟩
        exact Program.Runs.leftExit
          (Program.Runs.rightExit (coded_decrement_positive zero)
            (Program.Runs.rightExit tail canBreak rfl) rfl) rfl

structure CodedFront (s t : Store M) : Prop where
  scratch : Scratch t
  index : t np = s np
  pending : t pl ≤ s pl
  unused : t 11 = s 11

theorem CodedFront.refl (s : Store M) (ready : Scratch s) : CodedFront s s :=
  ⟨ready,rfl,le_rfl,rfl⟩

theorem CodedFront.trans {s t u : Store M} (first : CodedFront s t) (last : CodedFront t u) :
    CodedFront s u :=
  ⟨last.scratch,last.index.trans first.index,last.pending.trans first.pending,last.unused.trans first.unused⟩

theorem coded_instruction_total [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (i : Instruction) (s : Store M) (ready : Scratch s) :
    ∃ t, (instruction i).Runs .normal s.code t.code ∧ CodedFront s t := by
  cases i with
  | literal token =>
    refine ⟨modelLiteralEffect token s,coded_literalToken token s ready,?_⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      simp [modelLiteralEffect,Scratch.iff_fields,Store.set,fr,gues,tok,u,np,pl,expected,
        ready.expectedEmpty,ready.tokenEmpty,ready.auxiliaryEmpty]
  | capture slot =>
    obtain ⟨t,run,good,_,keeps⟩ := coded_scan_total slot s ready
    refine ⟨t,run,good,keeps np (by decide),?_,keeps 11 (by decide)⟩
    rw [keeps pl (by decide)]
  | reverse =>
    refine ⟨(s.set fr (s lv)).set lv (s fr),coded_exchange s ready.auxiliaryEmpty,?_⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      simp [Scratch.iff_fields,Store.set,fr,lv,tok,u,np,pl,expected,
        ready.expectedEmpty,ready.tokenEmpty,ready.auxiliaryEmpty]

theorem coded_instructions_total [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (is : List Instruction) (s : Store M) (ready : Scratch s) :
    ∃ t, CodedLines (is.map instruction) s.code t.code ∧ CodedFront s t := by
  induction is generalizing s with
  | nil => exact ⟨s,.nil _,CodedFront.refl s ready⟩
  | cons first rest ih =>
    obtain ⟨mid,head,fields⟩ := coded_instruction_total first s ready
    obtain ⟨t,tail,preserved⟩ := ih mid fields.scratch
    exact ⟨t,.cons head tail,fields.trans preserved⟩

end PalomarI3334.SearchProgram

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (CodedLines block modelSelect_exists modelSelect_map)
open ArithmeticMachine.SourceCantor
open Templates (Instruction)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def CodedTrieOutcome (ps : List Program) (s : Store M) : Prop :=
  ∃ t, CodedLines ps s.code t.code ∧ CodedFront s t

theorem coded_choose_total (keys : List (Option Instruction)) (branches : Option Instruction → List Program)
    (s : Store M) (ready : Scratch s)
    (exec : ∀ k ∈ keys, ∀ t : Store M, Scratch t → CodedTrieOutcome (branches k) t) :
    CodedTrieOutcome (choose keys branches) s := by
  cases keys with
  | nil => exact ⟨s,.nil _,CodedFront.refl s ready⟩
  | cons first rest =>
    cases rest with
    | nil => exact exec first List.mem_cons_self s ready
    | cons second rest =>
      let keys := first::second::rest
      by_cases suffix : suffixFork keys = true
      · obtain ⟨key,v,belongs,found⟩ := modelSelect_exists (ps := [first,second]) (by simp) (s tmp)
        let mid := s.set tmp v
        have keeps : CodedFront s mid := by
          refine ⟨?_,?_,?_,?_⟩ <;>
            simp [Scratch.iff_fields,mid,Store.set,tmp,np,pl,expected,tok,u,ready.expectedEmpty,
              ready.tokenEmpty,ready.auxiliaryEmpty]
        have member : key ∈ keys := by
          simpa only [keys,List.cons_append,List.nil_append] using List.mem_append_left rest belongs
        obtain ⟨t,run,relative⟩ := exec key member mid keeps.scratch
        have select := modelSelect_map (block ∘ branches) [first,second] (s tmp)
        rw [found] at select
        have dispatched := coded_dispatchBy tmp _ s select run.block
        refine ⟨t,?_,keeps.trans relative⟩
        simpa only [choose,keys,suffix,↓reduceIte,List.map_cons,List.map_nil,Function.comp_apply]
          using CodedLines.cons dispatched (.nil _)
      · let p := decodeRight (s pl)
        let loaded := (s.set pl p).set goal (s goal+decodeLeft (s pl))
        have read := coded_read (dst := goal) (by decide) (by decide) s ready.tokenEmpty ready.auxiliaryEmpty
        obtain ⟨key,v,belongs,found⟩ := modelSelect_exists (ps := keys) (by simp [keys]) (loaded goal)
        let mid := loaded.set goal v
        have keeps : CodedFront s mid := by
          refine ⟨?_,?_,?_,?_⟩
          · simpa [Scratch.iff_fields,mid,loaded,Store.set,pl,goal,expected,tok,u]
              using Scratch.iff_fields.mp ready
          · simp [mid,loaded,Store.set,pl,goal,np]
          · simpa [mid,loaded,Store.set,pl,goal,p] using (decodeValue_bounds (s pl)).2
          · simp [mid,loaded,Store.set,pl,goal]
        obtain ⟨t,run,relative⟩ := exec key belongs mid keeps.scratch
        have select := modelSelect_map (block ∘ branches) keys (loaded goal)
        rw [found] at select
        have dispatched := coded_dispatchBy goal _ loaded select run.block
        refine ⟨t,?_,keeps.trans relative⟩
        simpa only [choose,keys,suffix,Bool.false_eq_true,↓reduceIte,Function.comp_def,dispatch]
          using CodedLines.cons read (CodedLines.cons dispatched (.nil _))

theorem coded_trie_total [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (fuel : Nat) (table : List (List Instruction))
    (s : Store M) (ready : Scratch s) :
    CodedTrieOutcome (trie fuel table) s := by
  induction fuel generalizing table s with
  | zero => exact ⟨s,.nil _,CodedFront.refl s ready⟩
  | succ fuel ih =>
    cases table with
    | nil => exact ⟨s,.nil _,CodedFront.refl s ready⟩
    | cons first rest =>
      cases rest with
      | nil => exact coded_instructions_total first s ready
      | cons second rest =>
        apply coded_choose_total _ _ s ready
        intro key member mid good
        cases key with
        | none => exact ⟨mid,.nil _,CodedFront.refl mid good⟩
        | some i =>
          obtain ⟨next,op,keeps⟩ := coded_instruction_total i mid good
          obtain ⟨out,tail,last⟩ := ih (branchRows (some i) (first :: second :: rest)) next keeps.scratch
          exact ⟨out,.cons op tail,keeps.trans last⟩

end PalomarI3334.SearchProgram
