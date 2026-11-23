module
public import I3_334.Search.TrieSoundness
public import I3_334.Search.MainTrial
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (LineRuns block selectBranch_exact selectBranch_map)
open Templates (Instruction)

inductive RecipeStep where
  | emit (token : Instruction)
  | selector (branch : Nat)
  | tail (branch : Nat)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def branchRecipe (keys : List (Option Instruction)) (index : Nat) : List RecipeStep :=
  if keys.length ≤ 1 then []
  else if suffixFork keys then [.tail index]
  else [.selector index]

/-- Fix the selector decisions that produce a requested declared row. -/
def recipe : Nat → List (List Instruction) → List Instruction → Option (List RecipeStep)
  | 0, _, target => if target = [] then some [] else none
  | _ + 1, [], _ => none
  | _ + 1, [line], target => if target = line then some (line.map .emit) else none
  | fuel + 1, first :: second :: rest, target =>
    let table := first :: second :: rest
    let keys := branchKeys table
    let key := target.head?
    let n := keys.idxOf key
    if n < keys.length then
      let start := branchRecipe keys n
      match target with
      | [] => some start
      | tok :: suffix => (recipe fuel (branchRows (some tok) table) suffix).map
          (fun tail => start ++ .emit tok :: tail)
    else none

def recipeStep : RecipeStep → Store → Option Store
  | .emit token, s => some (instructionEffect token s)
  | .selector index, s =>
    let field := Cantor.unpair (s pl)
    if s goal = 0 ∧ field.1 = index then some (s.set pl field.2) else none
  | .tail index, s =>
    if s tmp = index then some (s.set tmp 0) else none

def runRecipe (steps : List RecipeStep) (s : Store) : Option Store :=
  steps.foldlM (fun state action => recipeStep action state) s

@[simp] theorem runRecipe_nil : runRecipe [] = some := rfl

theorem runRecipe_cons (a : RecipeStep) (rest : List RecipeStep) (s : Store) :
    runRecipe (a :: rest) s = (recipeStep a s).bind (runRecipe rest) := rfl

theorem runRecipe_append (xs ys : List RecipeStep) (s : Store) :
    runRecipe (xs ++ ys) s = (runRecipe xs s).bind (runRecipe ys) :=
  List.foldlM_append

theorem recipeStep_clean {a : RecipeStep} {s t : Store} (h : recipeStep a s = some t)
    (ready : Scratch s) : Scratch t := by
  cases a with
  | emit tok =>
    have result : instructionEffect tok s = t := Option.some.inj h
    exact result ▸ instruction_clean tok s ready
  | selector index =>
    by_cases fits : s goal = 0 ∧ (Cantor.unpair (s pl)).1 = index
    · simp only [recipeStep,fits,true_and,↓reduceIte,Option.some.injEq] at h
      subst t
      refine ⟨?_,?_,?_⟩ <;>
        simp [Store.set,pl,expected,tok,u,ready.expectedEmpty,ready.tokenEmpty,ready.auxiliaryEmpty]
    · simp [recipeStep,fits] at h
  | tail index =>
    by_cases fits : s tmp = index
    · simp only [recipeStep,fits,true_and,↓reduceIte,Option.some.injEq] at h
      subst t
      refine ⟨?_,?_,?_⟩ <;>
        simp [Store.set,tmp,expected,tok,u,ready.expectedEmpty,ready.tokenEmpty,ready.auxiliaryEmpty]
    · simp [recipeStep,fits] at h

theorem runRecipe_clean {steps : List RecipeStep} {s t : Store} (h : runRecipe steps s = some t)
    (ready : Scratch s) : Scratch t := by
  induction steps generalizing s with
  | nil =>
    have eq : s = t := Option.some.inj h
    exact eq ▸ ready
  | cons a rest ih =>
    cases step : recipeStep a s with
    | none => simp [runRecipe_cons,step] at h
    | some mid =>
      have restRun : runRecipe rest mid = some t := by
        simpa only [runRecipe_cons,step,Option.bind_some] using h
      exact ih restRun (recipeStep_clean step ready)

def emitted (steps : List RecipeStep) : List Instruction :=
  steps.filterMap fun action => match action with
    | .emit i => some i
    | _ => none

theorem recipeStep_observes {a : RecipeStep} {s t : Store} (h : recipeStep a s = some t) :
    FrontBounds (instructionsEffect (emitted [a]) s) t := by
  cases a with
  | emit i =>
    have eq : instructionEffect i s = t := Option.some.inj h
    subst t
    exact FrontBounds.refl _
  | selector index =>
    by_cases fits : s goal = 0 ∧ (Cantor.unpair (s pl)).1 = index
    · simp only [recipeStep,fits,true_and,↓reduceIte,Option.some.injEq] at h
      subst t
      constructor <;> simp [instructionsEffect,emitted,Store.set,pl,fr,lv,dc,gues,np]
    · simp [recipeStep,fits] at h
  | tail index =>
    by_cases fits : s tmp = index
    · simp only [recipeStep,fits,true_and,↓reduceIte,Option.some.injEq] at h
      subst t
      constructor <;> simp [instructionsEffect,emitted,Store.set,tmp,fr,lv,dc,gues,np]
    · simp [recipeStep,fits] at h

theorem runRecipe_observes {steps : List RecipeStep} {s t : Store}
    (h : runRecipe steps s = some t) :
    FrontBounds (instructionsEffect (emitted steps) s) t := by
  induction steps generalizing s with
  | nil =>
    have eq : s = t := Option.some.inj h
    exact eq ▸ FrontBounds.refl s
  | cons a rest ih =>
    cases step : recipeStep a s with
    | none => simp [runRecipe_cons,step] at h
    | some mid =>
      have remainder : runRecipe rest mid = some t := by
        simpa only [runRecipe_cons,step,Option.bind_some] using h
      have first := instructions_observe (emitted rest) (recipeStep_observes step)
      have all := first.trans (ih remainder)
      cases a <;> exact all

theorem branchRecipe_runs (keys : List (Option Instruction)) (branches : Option Instruction → List Program)
    (index : Nat) (bounded : index < keys.length) {s mid t : Store} (ready : Scratch s)
    (selected : runRecipe (branchRecipe keys index) s = some mid)
    (chosen : LineRuns (branches keys[index]) mid t) : LineRuns (choose keys branches) s t := by
  cases keys with
  | nil => simp at bounded
  | cons first rest =>
    cases rest with
    | nil =>
      have zero : index = 0 := by simpa using bounded
      subst index
      have eq : s = mid := by simpa [branchRecipe,runRecipe] using selected
      subst mid
      exact chosen
    | cons second rest =>
      let keys := first :: second :: rest
      by_cases fork : suffixFork keys = true
      · have short : rest = [] := by
          simp only [suffixFork,keys,beq_iff_eq] at fork
          have len := congrArg List.length fork
          simp at len
          omega
        subst rest
        have state : s tmp = index ∧ s.set tmp 0 = mid := by
          simpa [branchRecipe,keys,fork,runRecipe_cons,recipeStep,ite_eq_left_iff] using selected
        have exactIndex := selectBranch_exact ([first,second].map (block ∘ branches)) index (by simpa using bounded)
        have chosenIndex :
            Source.selectBranch ([first,second].map (block ∘ branches)) (s tmp) =
              some (block (branches ([first,second][index])),0) := by
          rw [state.1]
          simpa only [List.getElem_map,Function.comp_apply] using exactIndex
        have dispatch := run_dispatchBy tmp _ s chosenIndex
          (by simpa only [state.2] using chosen.block)
        simpa only [choose,show suffixFork [first,second] = true from fork,↓reduceIte,
          List.map_cons,List.map_nil,Function.comp_apply] using LineRuns.cons dispatch .nil
      · let field := Cantor.unpair (s pl)
        have state : (s goal = 0 ∧ field.1 = index) ∧ s.set pl field.2 = mid := by
          simpa [branchRecipe,keys,fork,runRecipe_cons,recipeStep,field,ite_eq_left_iff] using selected
        let loaded := (s.set pl field.2).set goal index
        have read : Executes (read goal) s .normal loaded := by
          have pop := run_read (target := goal) (by decide) (by decide) s
            ready.tokenEmpty ready.auxiliaryEmpty
          simpa only [loaded,field,state.1.1,state.1.2,Nat.zero_add] using pop
        have idx := selectBranch_exact (keys.map (block ∘ branches)) index (by simpa [keys] using bounded)
        have count : loaded goal = index := Store.get_set _ _ _
        have boundedKeys : index < keys.length := by simpa [keys] using bounded
        have chosenIndex : Source.selectBranch (keys.map (block ∘ branches)) (loaded goal) =
            some (block (branches keys[index]),0) := by
          rw [count]
          simpa only [List.getElem_map,Function.comp_apply] using idx
        have restore : loaded.set goal 0 = mid := by
          simp only [loaded,Store.set_set]
          rw [Store.set_comm (s := s) (by decide : pl ≠ goal) field.2 0]
          have preserved : s.set goal 0 = s := by
            simpa only [state.1.1] using Store.set_same s goal
          rw [preserved,state.2]
        have run := run_dispatchBy goal _ loaded chosenIndex (by
          simpa only [restore,keys] using chosen.block)
        simpa only [keys,choose,fork,Bool.false_eq_true,↓reduceIte,dispatch,Function.comp_def] using
          LineRuns.cons read (LineRuns.cons run .nil)

end PalomarI3334.SearchProgram
