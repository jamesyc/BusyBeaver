module
public import I3_334.Search.SearchScanLoop
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (LineRuns inc clear run_clear run_inc run_increments)
open Templates (Instruction)

theorem run_dictionarySlot (slot : Fin 4) (s : Store) (clean : Scratch s) :
    LineRuns (dictionarySlot slot) s (s.set tmp ((Dictionary.decode (s tmp)).coordinate slot)) := by
  let left := fun n : Nat => (Cantor.unpair n).1
  let right := fun n : Nat => (Cantor.unpair n).2
  let word := s tmp
  have step (takeLeft : Bool) (code : Nat) :
      Executes (dictionaryPart takeLeft) (s.set tmp code) .normal
        (s.set tmp (if takeLeft then left code else right code)) := by
    have proof := run_dictionaryPart takeLeft (s.set tmp code)
      (by simpa [Store.set,tmp,expected] using clean.expectedEmpty)
      (by simpa [Store.set,tmp,u] using clean.auxiliaryEmpty)
    simpa only [Store.get_set,Store.set_set,left,right] using proof
  have start (takeLeft : Bool) :
      Executes (dictionaryPart takeLeft) s .normal
        (s.set tmp (if takeLeft then left word else right word)) := by
    simpa only [word,Store.set_same] using step takeLeft word
  have eq : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases eq with rfl | rfl | rfl | rfl
  · exact .cons (start false) .nil
  · exact .cons (start true) (.cons (step false (left word)) .nil)
  · exact .cons (start true) (.cons (step true (left word))
      (.cons (step false (left (left word))) .nil))
  · exact .cons (start true) (.cons (step true (left word))
      (.cons (step true (left (left word))) .nil))

def captureEffect (slot : Fin 4) (s : Store) : Store :=
  let codes := Dictionary.decode (s dc)
  let word := codes.coordinate slot
  let matched := scanMatch (codes.capture slot).tokens (s fr)
  (((s.set goal 0).set tmp (scanRaw (bias slot) word 1).2).set fr matched.rest).set gues
    (markedIf (s gues) (matched.valid = true))

theorem run_scan (slot : Fin 4) (s : Store) (clean : Scratch s) :
    Executes (scan slot) s .normal (captureEffect slot s) := by
  let cleared := (s.set goal 0).set tmp 0
  let copied := cleared.set tmp (s dc)
  let codes := Dictionary.decode (s dc)
  let spec := codes.coordinate slot
  let selected := copied.set tmp spec
  let started := selected.set goal 1
  have first : LineRuns [clear goal,clear tmp,copy dc tmp] s copied := by
    have copyData := run_copy (a := dc) (b := tmp) (by decide) (by decide) (by decide) cleared
      (by simpa [cleared,Store.set,goal,tmp,u] using clean.auxiliaryEmpty)
    have result : cleared.set tmp (cleared tmp+cleared dc) = copied := by
      simp [cleared,copied,Store.set,tmp,goal,dc]
    rw [result] at copyData
    exact .cons (run_clear goal s) (.cons (run_clear tmp (s.set goal 0)) (.cons copyData .nil))
  have good : Scratch copied := ⟨
    by simpa [copied,cleared,Store.set,goal,tmp,expected] using clean.expectedEmpty,
    by simpa [copied,cleared,Store.set,goal,tmp,tok] using clean.tokenEmpty,
    by simpa [copied,cleared,Store.set,goal,tmp,u] using clean.auxiliaryEmpty⟩
  have setup : LineRuns (dictionarySlot slot) copied selected := by
    have load := run_dictionarySlot slot copied good
    simpa only [copied,codes,spec,selected,Store.get_set] using load
  have increment : Executes (inc goal) selected .normal started := by
    have known : selected goal = 0 := by simp [selected,copied,cleared,Store.set,tmp,goal]
    simpa only [known,Nat.zero_add,started] using run_inc goal selected
  have ready : Scratch started := ⟨
    by simpa [started,selected,copied,cleared,Store.set,goal,tmp,expected] using clean.expectedEmpty,
    by simpa [started,selected,copied,cleared,Store.set,goal,tmp,tok] using clean.tokenEmpty,
    by simpa [started,selected,copied,cleared,Store.set,goal,tmp,u] using clean.auxiliaryEmpty⟩
  have loop := run_scanLoop slot started ready
  have actual : scanLoopEffect slot started = captureEffect slot s := by
    have term := Dictionary.capture_tokens (Dictionary.decode (s dc)) slot
    rw [← bias_eq_offset] at term
    have pending : started goal = 1 := Store.get_set _ _ _
    have transferred : started tmp = spec := by simp [started,selected,Store.set,tmp,goal]
    have front : started fr = s fr := by simp [started,selected,copied,cleared,Store.set,tmp,goal,fr]
    have marker : started gues = s gues := by
      simp [started,selected,copied,cleared,Store.set,tmp,goal,gues]
    simp only [scanLoopEffect,captureEffect,pending,transferred,front,marker,codes,spec,term]
    funext i
    by_cases a : i = goal <;> by_cases b : i = tmp <;> by_cases c : i = fr <;>
      by_cases v : i = gues <;> simp [started,selected,copied,cleared,Store.set,a,b,c,v,goal,tmp,fr,gues]
  rw [actual] at loop
  exact ((first.append setup).append (.cons increment (.cons loop .nil))).block

def literalEffect (token : Token) (s : Store) : Store :=
  let result := scanMatch [token] (s fr)
  (s.set fr result.rest).set gues (markedIf (s gues) (result.valid = true))

theorem run_literalToken (token : Token) (s : Store) (clean : Scratch s) :
    Executes (literalToken token) s .normal (literalEffect token s) := by
  let raised := s.set expected (token.arity+1)
  let middle := consumeField raised
  let retag := middle.set expected token.tag
  have first : LineRuns (List.replicate (token.arity+1) (inc expected)) s raised := by
    simpa only [raised,clean.expectedEmpty,Nat.zero_add] using run_increments expected (token.arity+1) s
  have check₁ : Executes eat raised .normal middle := run_eat raised
    (by simpa [raised,Store.set,tok,expected] using clean.tokenEmpty)
    (by simpa [raised,Store.set,u,expected] using clean.auxiliaryEmpty)
  have zero : middle expected = 0 := by simp [middle,consumeField,Store.set,expected,gues]
  have tag : LineRuns (List.replicate token.tag (inc expected)) middle retag := by
    simpa only [retag,zero,Nat.zero_add] using run_increments expected token.tag middle
  have check₂ : Executes eat retag .normal (consumeField retag) := run_eat retag
    (by simpa [retag,middle,consumeField,raised,Store.set,tok,expected,fr,gues] using clean.tokenEmpty)
    (by simpa [retag,middle,consumeField,raised,Store.set,u,expected,fr,gues] using clean.auxiliaryEmpty)
  have result : consumeField retag = literalEffect token s := by
    funext i
    by_cases a : i = expected <;> by_cases f : i = fr <;> by_cases g : i = gues <;>
      simp [literalEffect,scanMatch,rawFields,consumeField,retag,middle,raised,Store.set,
        a,f,g,fr,expected,gues,clean.expectedEmpty,markedIf_and,decide_eq_true_eq]
    all_goals
      by_cases equal : token.arity+1 = (Cantor.unpair (s fr)).1 ∧
          token.tag = (Cantor.unpair (Cantor.unpair (s fr)).2).1 <;>
        simp [markedIf,equal,fr] at *
  rw [result] at check₂
  simpa only [literalToken, List.append_assoc] using
    ((first.append (.cons check₁ .nil)).append (tag.append (.cons check₂ .nil))).block

def instructionEffect (i : Instruction) (s : Store) : Store :=
  match i with
  | .literal token => literalEffect token s
  | .capture slot => captureEffect slot s
  | .reverse => (s.set fr (s lv)).set lv (s fr)

theorem run_instruction (i : Instruction) (s : Store) (clean : Scratch s) :
    Executes (instruction i) s .normal (instructionEffect i s) := by
  cases i with
  | literal t => exact run_literalToken t s clean
  | capture slot => exact run_scan slot s clean
  | reverse => exact run_exchange s clean.auxiliaryEmpty

theorem instruction_clean (i : Instruction) (s : Store) (clean : Scratch s) :
    Scratch (instructionEffect i s) := by
  cases i <;> refine ⟨?_,?_,?_⟩ <;>
    simp [instructionEffect,literalEffect,captureEffect,Store.set,goal,tmp,fr,lv,gues,
      expected,tok,u,clean.expectedEmpty,clean.tokenEmpty,clean.auxiliaryEmpty]

end PalomarI3334.SearchProgram
