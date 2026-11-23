module
public import I3_334.Search.SearchInstructions
public import I3_334Support.Search.Compiler.Dispatch
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (LineRuns selectBranch selectBranch_exists
  selectBranch_map selectBranch_mem selectBranch_exact dec_zero dec_pos run_break then_normal block)
open Templates (Instruction)

/-- Saturation follows the final branch and leaves any surplus selector
in the counter, including the shared goal counter. -/
theorem run_dispatchBy (counter : Register) (ps : List Program) (s : Store)
    {p : Program} {r : Nat} {t : Store}
    (chosen : selectBranch ps (s counter) = some (p,r))
    (run : Executes p (s.set counter r) .normal t) :
    Executes (dispatchBy counter ps) s .normal t := by
  induction ps generalizing s t p r with
  | nil => simp [selectBranch] at chosen
  | cons head ps ih =>
    cases ps with
    | nil =>
      simp only [selectBranch,Option.some.injEq,Prod.mk.injEq] at chosen
      obtain ⟨rfl,rfl⟩ := chosen
      rw [Store.set_same] at run
      exact run
    | cons following rest =>
      cases value : s counter with
      | zero =>
        simp only [value,selectBranch,Option.some.injEq,Prod.mk.injEq] at chosen
        obtain ⟨rfl,rfl⟩ := chosen
        rw [← value,Store.set_same] at run
        exact then_normal (.leftExit (dec_zero value) rfl) run
      | succ n =>
        let middle := s.set counter (s counter - 1)
        have selects : selectBranch (following :: rest) (middle counter) = some (p,r) := by
          have label : middle counter = n := by simp [middle,value]
          simpa only [value,selectBranch,label] using chosen
        have branch : Executes p (middle.set counter r) .normal t := by
          simpa only [middle,Store.set_set] using run
        have restRun := ih middle selects branch
        exact .leftExit (.rightExit (dec_pos (by omega))
          (.rightExit restRun (run_break 0 _) rfl) rfl) rfl

/-- These are the registers observed by a template instruction. Branch
selection may consume the proof suffix and alter either scratch counter. -/
structure FrontBounds (s t : Store) : Prop where
  left : t fr = s fr
  right : t lv = s lv
  dictionary : t dc = s dc
  marker : t gues = s gues
  word : t np = s np
  unused : t 11 = s 11

theorem FrontBounds.refl (s : Store) : FrontBounds s s := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem FrontBounds.trans {s t u : Store} (st : FrontBounds s t) (tu : FrontBounds t u) :
    FrontBounds s u := ⟨tu.left.trans st.left,tu.right.trans st.right,tu.dictionary.trans st.dictionary,
      tu.marker.trans st.marker,tu.word.trans st.word,tu.unused.trans st.unused⟩

theorem instruction_observe (i : Instruction) {s t : Store} (bounds : FrontBounds s t) :
    FrontBounds (instructionEffect i s) (instructionEffect i t) := by
  cases i <;> constructor <;>
    simp [instructionEffect,literalEffect,captureEffect,Store.set,fr,lv,dc,gues,np,goal,tmp,
      bounds.left,bounds.right,bounds.dictionary,bounds.marker,bounds.word,bounds.unused]

theorem instruction_pending (i : Instruction) (s : Store) : instructionEffect i s pl = s pl := by
  cases i <;> simp [instructionEffect,literalEffect,captureEffect,Store.set,fr,lv,dc,gues,pl,goal,tmp]

theorem instruction_unused (i : Instruction) (s : Store) : instructionEffect i s 11 = s 11 := by
  cases i <;> simp [instructionEffect,literalEffect,captureEffect,Store.set,fr,lv,gues,goal,tmp]

def instructionsEffect (is : List Instruction) (s : Store) : Store :=
  is.foldl (fun state i => instructionEffect i state) s

theorem instructions_observe (is : List Instruction) {s t : Store} (bounds : FrontBounds s t) :
    FrontBounds (instructionsEffect is s) (instructionsEffect is t) := by
  induction is generalizing s t with
  | nil => exact bounds
  | cons i rest ih => exact ih (instruction_observe i bounds)

theorem instructions_pending (is : List Instruction) (s : Store) :
    instructionsEffect is s pl = s pl := by
  induction is generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change instructionsEffect rest (instructionEffect i s) pl = s pl
    rw [ih,instruction_pending]

theorem instructions_unused (is : List Instruction) (s : Store) :
    instructionsEffect is s 11 = s 11 := by
  induction is generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change instructionsEffect rest (instructionEffect i s) 11 = s 11
    rw [ih,instruction_unused]

theorem instructions_run (is : List Instruction) (s : Store) (ready : Scratch s) :
    LineRuns (is.map instruction) s (instructionsEffect is s) ∧ Scratch (instructionsEffect is s) := by
  induction is generalizing s with
  | nil => exact ⟨.nil,ready⟩
  | cons i rest ih =>
    obtain ⟨tail,clean⟩ := ih (instructionEffect i s) (instruction_clean i s ready)
    exact ⟨.cons (run_instruction i s ready) tail,clean⟩

private theorem select_pending (x : Nat) : (Cantor.unpair x).2 ≤ x := by
  simpa only [Cantor.pair_unpair] using
    (Cantor.right_le (Cantor.unpair x).1 (Cantor.unpair x).2)

structure Choice (keys : List (Option Instruction)) (branches : Option Instruction → List Program)
    (source : Store) where
  key : Option Instruction
  start : Store
  member : key ∈ keys
  scratch : Scratch start
  observed : FrontBounds source start
  pending : start pl ≤ source pl
  execute : ∀ {t : Store}, LineRuns (branches key) start t →
    LineRuns (choose keys branches) source t

/-- Interpret the two branch implementations at the physical counters.
No assumption is made about a saturated selector. -/
theorem choose_runs (keys : List (Option Instruction)) (branches : Option Instruction → List Program)
    (s : Store) (ready : Scratch s) (nonempty : keys ≠ []) :
    Nonempty (Choice keys branches s) := by
  cases keys with
  | nil => exact (nonempty rfl).elim
  | cons first remaining =>
    cases remaining with
    | nil => exact ⟨⟨first,s,List.mem_cons_self,ready,FrontBounds.refl s,Nat.le_refl _,fun run => run⟩⟩
    | cons second rest =>
      by_cases suffix : suffixFork (first::second::rest) = true
      · obtain ⟨key,value,found⟩ := selectBranch_exists [first,second] (s tmp) (by simp)
        let start := s.set tmp value
        have good : Scratch start := ⟨
          by simpa [start,Store.set,tmp,expected] using ready.expectedEmpty,
          by simpa [start,Store.set,tmp,tok] using ready.tokenEmpty,
          by simpa [start,Store.set,tmp,u] using ready.auxiliaryEmpty⟩
        have fields : FrontBounds s start := by
          constructor <;> simp [start,Store.set,tmp,fr,lv,dc,gues,np]
        have number : start pl ≤ s pl := by simp [start,Store.set,tmp,pl]
        have member : key ∈ (first::second::rest) := by
          have h := selectBranch_mem found
          simpa using List.mem_append_left rest h
        refine ⟨⟨key,start,member,good,fields,number,?_⟩⟩
        intro t run
        have branchEq := congrArg (Option.map fun (k,v) => (block (branches k),v)) found
        have branch := (selectBranch_map (block ∘ branches) [first,second] (s tmp)).trans branchEq
        have dispatch := run_dispatchBy tmp _ s branch run.block
        simpa only [choose,suffix,↓reduceIte,List.map_cons,List.map_nil,Function.comp_apply]
          using LineRuns.cons dispatch .nil
      · let field := Cantor.unpair (s pl)
        let loaded := (s.set pl field.2).set goal (s goal+field.1)
        have read := run_read (target := goal) (by decide) (by decide) s
          ready.tokenEmpty ready.auxiliaryEmpty
        obtain ⟨key,value,found⟩ := selectBranch_exists (first::second::rest) (loaded goal) (by simp)
        let start := loaded.set goal value
        have good : Scratch start := ⟨
          by simpa [start,loaded,Store.set,goal,pl,expected] using ready.expectedEmpty,
          by simpa [start,loaded,Store.set,goal,pl,tok] using ready.tokenEmpty,
          by simpa [start,loaded,Store.set,goal,pl,u] using ready.auxiliaryEmpty⟩
        have fields : FrontBounds s start := by
          constructor <;> simp [start,loaded,Store.set,goal,pl,fr,lv,dc,gues,np]
        have number : start pl ≤ s pl := by
          simpa [start,loaded,Store.set,goal,pl,field] using select_pending (s pl)
        refine ⟨⟨key,start,selectBranch_mem found,good,fields,number,?_⟩⟩
        intro t run
        have branchEq := congrArg (Option.map fun (k,v) => (block (branches k),v)) found
        have branch := (selectBranch_map (block ∘ branches) (first::second::rest) (loaded goal)).trans branchEq
        have dispatch := run_dispatchBy goal _ loaded branch run.block
        simpa only [choose,suffix,Bool.false_eq_true,↓reduceIte,dispatch,Function.comp_def] using
          LineRuns.cons read (LineRuns.cons dispatch .nil)

end PalomarI3334.SearchProgram
