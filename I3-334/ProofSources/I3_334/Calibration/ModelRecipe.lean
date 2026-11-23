module
public import I3_334.Calibration.ModelTrie
public import I3_334.Search.TrieCompleteness
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (CodedLines block modelSelect_exact modelSelect_map)
open ArithmeticMachine.SourceCantor
open Templates (Instruction)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

inductive RecipeTransition : RecipeStep → Store M → Store M → Prop
  | emit {i : Instruction} {s t : Store M} (run : (instruction i).Runs .normal s.code t.code)
      (ready : Scratch t) : RecipeTransition (.emit i) s t
  | selector {k : Nat} {s : Store M} (zero : s goal = 0) (index : decodeLeft (s pl) = (k : M)) :
      RecipeTransition (.selector k) s (s.set pl (decodeRight (s pl)))
  | tail {k : Nat} {s : Store M} (index : s tmp = (k : M)) :
      RecipeTransition (.tail k) s (s.set tmp 0)

inductive RecipeTrace : List RecipeStep → Store M → Store M → Prop
  | nil (s : Store M) : RecipeTrace [] s s
  | cons {a : RecipeStep} {as : List RecipeStep} {s t u : Store M}
      (first : RecipeTransition a s t) (rest : RecipeTrace as t u) : RecipeTrace (a :: as) s u

theorem RecipeTrace.split {xs ys : List RecipeStep} {s t : Store M}
    (path : RecipeTrace (xs ++ ys) s t) : ∃ mid, RecipeTrace xs s mid ∧ RecipeTrace ys mid t := by
  induction xs generalizing s with
  | nil => exact ⟨s,.nil _,path⟩
  | cons a rest ih =>
    cases path with
    | cons first later =>
      obtain ⟨mid,left,right⟩ := ih later
      exact ⟨mid,.cons first left,right⟩

theorem RecipeTrace.clean {steps : List RecipeStep} {s t : Store M}
    (path : RecipeTrace steps s t) (ready : Scratch s) : Scratch t := by
  induction path with
  | nil => exact ready
  | cons first later ih =>
    apply ih
    cases first with
    | emit _ ready => exact ready
    | selector =>
      simpa [Scratch.iff_fields,Store.set,pl,expected,tok,u] using Scratch.iff_fields.mp ready
    | tail =>
      simpa [Scratch.iff_fields,Store.set,tmp,expected,tok,u] using Scratch.iff_fields.mp ready

theorem coded_branchRecipe (keys : List (Option Instruction)) (branches : Option Instruction → List Program)
    (index : Nat) (bounded : index < keys.length) {s mid t : Store M} (ready : Scratch s)
    (selected : RecipeTrace (branchRecipe keys index) s mid)
    (chosen : CodedLines (branches keys[index]) mid.code t.code) :
    CodedLines (choose keys branches) s.code t.code := by
  cases keys with
  | nil => simp at bounded
  | cons first rest =>
    cases rest with
    | nil =>
      have zero : index = 0 := by simpa using bounded
      subst index
      have empty : RecipeTrace [] s mid := by simpa [branchRecipe] using selected
      cases empty
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
        have step : RecipeTrace [.tail index] s mid := by simpa [branchRecipe,keys,fork] using selected
        cases step with
        | cons h rest =>
          cases h with
          | tail counter =>
            cases rest
            have select : Source.modelSelect ([first,second].map (block ∘ branches)) (s tmp) =
                some (block (branches ([first,second][index])),0) := by
              rw [counter]
              rw [modelSelect_map, modelSelect_exact (M := M) [first,second] index bounded]
              rfl
            have dispatch := coded_dispatchBy tmp _ s select chosen.block
            simpa only [choose,show suffixFork [first,second] = true from fork,↓reduceIte,
              List.map_cons,List.map_nil,Function.comp_apply] using CodedLines.cons dispatch (.nil _)
      · have step : RecipeTrace [.selector index] s mid := by simpa [branchRecipe,keys,fork] using selected
        cases step with
        | cons h rest =>
          cases h with
          | selector zero field =>
            cases rest
            let loaded := (s.set pl (decodeRight (s pl))).set goal (index : M)
            have read : (read goal).Runs .normal s.code loaded.code := by
              simpa only [loaded,zero,zero_add,field] using
                coded_read (dst := goal) (by decide) (by decide) s ready.tokenEmpty ready.auxiliaryEmpty
            have select : Source.modelSelect (keys.map (block ∘ branches)) (loaded goal) =
                some (block (branches keys[index]),0) := by
              rw [show loaded goal = (index : M) from Store.get_set ..]
              rw [modelSelect_map, modelSelect_exact (M := M) keys index bounded]
              rfl
            have restore : loaded.set goal 0 = s.set pl (decodeRight (s pl)) := by
              rw [show loaded.set goal 0 = (s.set pl (decodeRight (s pl))).set goal 0 from Store.set_set ..,
                Store.set_comm (s := s) (by decide : pl ≠ goal), ← zero,Store.set_same]
            have run := coded_dispatchBy goal _ loaded select (by simpa only [restore,keys] using chosen.block)
            simpa only [keys,choose,fork,Bool.false_eq_true,↓reduceIte,dispatch,Function.comp_def] using
              CodedLines.cons read (CodedLines.cons run (.nil _))

theorem coded_recipe_emits {xs : List Instruction} {s t : Store M}
    (run : RecipeTrace (xs.map .emit) s t) : CodedLines (xs.map instruction) s.code t.code := by
  induction xs generalizing s with
  | nil => cases run; exact .nil _
  | cons i rest ih =>
    cases run with
    | cons first later =>
      cases first with
      | emit op _ => exact .cons op (ih later)

theorem coded_recipe (fuel : Nat) (table : List (List Instruction)) (row : List Instruction)
    {actions : List RecipeStep} (planned : recipe fuel table row = some actions)
    {s t : Store M} (ready : Scratch s) (run : RecipeTrace actions s t) :
    CodedLines (trie fuel table) s.code t.code := by
  induction fuel generalizing table row actions s t with
  | zero =>
    by_cases empty : row = []
    · simp only [recipe,empty,↓reduceIte,Option.some.injEq] at planned
      subst actions
      cases run
      exact .nil _
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
          exact coded_recipe_emits run
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
            have executed : CodedLines (branch keys[index]) t.code t.code := by
              rw [get]
              exact .nil _
            exact coded_branchRecipe keys branch index bounded ready run executed
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
              obtain ⟨mid,start,suffix⟩ := run.split
              have emitted : CodedLines (branch keys[index]) mid.code t.code := by
                rw [get]
                cases suffix with
                | cons first later =>
                  cases first with
                  | emit op clean => exact .cons op (ih _ _ tailPlan clean later)
              exact coded_branchRecipe keys branch index bounded ready start emitted
        · simp [recipe,table,keys,index,bounded] at planned

end PalomarI3334.SearchProgram
