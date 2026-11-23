module
public import I3_334.Search.TrieRecipe
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (LineRuns)
open Templates (Instruction equationInstructions)

theorem runRecipe_emits (xs : List Instruction) (s : Store) :
    runRecipe (xs.map .emit) s = some (instructionsEffect xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons i rest ih => exact ih (instructionEffect i s)

/-- Replay a planned row through the identical compiled trie. Selector
fields spend no proof-front data, and both kinds of exact pick clear
their counter. -/
theorem recipe_runs (fuel : Nat) (table : List (List Instruction)) (row : List Instruction)
    {actions : List RecipeStep} (planned : recipe fuel table row = some actions)
    {s t : Store} (ready : Scratch s) (run : runRecipe actions s = some t) :
    LineRuns (trie fuel table) s t := by
  induction fuel generalizing table row actions s t with
  | zero =>
    by_cases empty : row = []
    · simp only [recipe,empty,↓reduceIte,Option.some.injEq] at planned
      subst actions
      have eq : s = t := Option.some.inj run
      subst t
      exact .nil
    · simp [recipe,empty] at planned
  | succ fuel ih =>
    cases table with
    | nil => simp [recipe] at planned
    | cons first rest =>
      cases rest with
      | nil =>
        by_cases same : row = first
        · simp only [recipe,same,↓reduceIte,Option.some.injEq] at planned
          subst actions
          rw [runRecipe_emits] at run
          have eq : instructionsEffect first s = t := Option.some.inj run
          exact eq ▸ (instructions_run first s ready).1
        · simp [recipe,same] at planned
      | cons second rest =>
        let table := first::second::rest
        let keys := branchKeys table
        let index := keys.idxOf row.head?
        let branch := fun key : Option Instruction => match key with
          | none => []
          | some i => instruction i :: trie fuel (branchRows key table)
        by_cases bounded : index < keys.length
        · have get : keys[index] = row.head? := List.getElem_idxOf bounded
          cases row with
          | nil =>
            have chosen : branchRecipe keys index = actions := by
              simpa only [recipe,table,keys,index,bounded,↓reduceIte,Option.some.injEq] using planned
            subst actions
            have executed : LineRuns (branch keys[index]) t t := by
              rw [get]
              exact .nil
            exact branchRecipe_runs keys branch index bounded ready run executed
          | cons token more =>
            cases tailPlan : recipe fuel (branchRows (some token) table) more with
            | none =>
              simp only [recipe,table,keys,index,bounded,↓reduceIte,tailPlan,Option.map_none] at planned
              contradiction
            | some tail =>
              have chosen : branchRecipe keys index ++ .emit token :: tail = actions := by
                simpa only [recipe,table,keys,index,bounded,↓reduceIte,tailPlan,Option.map_some,
                  Option.some.injEq] using planned
              subst actions
              rw [runRecipe_append] at run
              cases start : runRecipe (branchRecipe keys index) s with
              | none => simp [start] at run
              | some mid =>
                have good := runRecipe_clean start ready
                have suffix : runRecipe tail (instructionEffect token mid) = some t := by
                  simpa only [start,Option.bind_some,runRecipe_cons,recipeStep] using run
                have replay := ih (branchRows (some token) table) more tailPlan
                  (instruction_clean token mid good) suffix
                have emitted : LineRuns (branch keys[index]) mid t := by
                  rw [get]
                  exact .cons (run_instruction token mid good) replay
                exact branchRecipe_runs keys branch index bounded ready start emitted
        · simp [recipe,table,keys,index,bounded] at planned

def selectors (steps : List RecipeStep) (tail : Nat) : Nat :=
  match steps with
  | [] => tail
  | .selector k :: rest => Cantor.pair k (selectors rest tail)
  | _ :: rest => selectors rest tail

def tailChoice (steps : List RecipeStep) : Nat :=
  match steps with
  | [] => 0
  | .tail k :: _ => k
  | _ :: rest => tailChoice rest

/-- The special choice is read only just after scanning slot a. -/
def validRecipe (value : Nat) : List RecipeStep → Bool
  | [] => true
  | .emit (.capture slot) :: .tail k :: rest =>
    (slot == 0) && (k == value) && validRecipe value rest
  | .tail _ :: _ => false
  | _ :: rest => validRecipe value rest

private theorem recipe_instruction_controls (i : Instruction) (s : Store) (zero : s goal = 0) :
    instructionEffect i s dc = s dc ∧ instructionEffect i s goal = 0 ∧ instructionEffect i s pl = s pl := by
  cases i <;>
    simp [instructionEffect,literalEffect,captureEffect,Store.set,goal,dc,pl,fr,lv,gues,tmp,zero]

/-- The recipe's outer fields and the independently chosen raw slot-a
suffix suffice to realize it, leaving precisely the supplied tail. -/
theorem run_encoded_recipe (steps : List RecipeStep) (value tail : Nat) (dict : Dictionary)
    (valid : validRecipe value steps = true)
    (suffix : (scanRaw 0 dict.a 1).2 = value) {s : Store}
    (goalStart : s goal = 0) (words : s pl = selectors steps tail) (codes : s dc = dict.encode) :
    ∃ t, runRecipe steps s = some t ∧ t pl = tail := by
  induction steps using List.twoStepInduction generalizing s with
  | nil => exact ⟨s,rfl,words⟩
  | singleton action =>
    cases action with
    | tail k => simp [validRecipe] at valid
    | selector k =>
      have fields : Cantor.unpair (s pl) = (k,tail) := by
        rw [words]
        exact Cantor.unpair_pair _ _
      exact ⟨s.set pl tail,by simp [runRecipe_cons,recipeStep,goalStart,fields],Store.get_set _ _ _⟩
    | emit i =>
      exact ⟨instructionEffect i s,rfl,(instruction_pending i s).trans words⟩
  | cons_cons a b rest head tailIH =>
    cases a with
    | tail k => simp [validRecipe] at valid
    | selector k =>
      have fields : Cantor.unpair (s pl) = (k,selectors (b::rest) tail) := by
        rw [words]
        exact Cantor.unpair_pair _ _
      let mid := s.set pl (selectors (b::rest) tail)
      have advance : recipeStep (.selector k) s = some mid := by simp [recipeStep,goalStart,fields,mid]
      have good : mid goal = 0 := by simp [mid,Store.set,goal,pl,goalStart]
      have coded : mid dc = dict.encode := by simp [mid,Store.set,dc,pl,codes]
      obtain ⟨t,run,pending⟩ := tailIH b (by simpa only [validRecipe] using valid) good
        (Store.get_set _ _ _) coded
      exact ⟨t,by simpa only [runRecipe_cons,advance,Option.bind_some] using run,pending⟩
    | emit i =>
      let mid := instructionEffect i s
      have ⟨sameDict,sameGoal,sameWord⟩ := recipe_instruction_controls i s goalStart
      by_cases suffixCase : ∃ slot k, i = .capture slot ∧ b = .tail k
      · obtain ⟨slot,k,rfl,rfl⟩ := suffixCase
        have ok : slot = 0 ∧ k = value ∧ validRecipe value rest = true := by
          have check := valid
          simp only [validRecipe,Bool.and_eq_true,beq_iff_eq] at check
          exact ⟨check.1.1,check.1.2,check.2⟩
        obtain ⟨rfl,rfl,good⟩ := ok
        have exactTail : mid tmp = k := by
          change captureEffect 0 s tmp = k
          simp [captureEffect,codes,Dictionary.decode_encode,Dictionary.coordinate,bias,
            Store.set,tmp,goal,fr,gues,suffix]
        let after := mid.set tmp 0
        have choose : recipeStep (.tail k) mid = some after := by simp [recipeStep,exactTail,after]
        have clean : after goal = 0 := by simp [after,mid,Store.set,goal,tmp,sameGoal]
        have state : after pl = selectors rest tail := by
          simp [after,mid,Store.set,pl,tmp,sameWord,words,selectors]
        have dictStill : after dc = dict.encode := by simp [after,mid,Store.set,dc,tmp,sameDict,codes]
        obtain ⟨t,run,pending⟩ := head good clean state dictStill
        have emit : recipeStep (.emit (.capture 0)) s = some mid := rfl
        exact ⟨t,by simpa only [runRecipe_cons,emit,choose,Option.bind_some] using run,pending⟩
      · have validTail : validRecipe value (b::rest) = true := by
          cases i <;> cases b <;> simp_all [validRecipe]
        obtain ⟨t,run,pending⟩  := tailIH b validTail sameGoal (sameWord.trans words) (sameDict.trans codes)
        exact ⟨t,by simpa only [runRecipe_cons,recipeStep,Option.bind_some] using run,pending⟩

def rowRecipe (line : List Instruction) : List RecipeStep :=
  (recipe templateFuel templateTable line).getD []

def checkRecipe (line : List Instruction) : Bool :=
  let steps := rowRecipe line
  (recipe templateFuel templateTable line == some steps) &&
    (emitted steps == line) && validRecipe (tailChoice steps) steps

set_option maxRecDepth 8192 in
theorem checked_recipes : templateTable.all checkRecipe = true := by decide +kernel

theorem rowRecipe_ok (line : List Instruction) (member : line ∈ templateTable) :
    recipe templateFuel templateTable line = some (rowRecipe line) ∧
      emitted (rowRecipe line) = line ∧ validRecipe (tailChoice (rowRecipe line)) (rowRecipe line) = true := by
  have checked := List.all_eq_true.mp checked_recipes _ member
  simp only [checkRecipe,Bool.and_eq_true,beq_iff_eq] at checked
  exact ⟨checked.1.1,checked.1.2,checked.2⟩

end PalomarI3334.SearchProgram
