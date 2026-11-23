module
public import I3_334.Search.TrieSoundness
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open Templates (Instruction Pattern substituteInstruction equationInstructions)

theorem scanMatch_append (xs ys : List Token) (word : Nat) :
    scanMatch (xs++ys) word =
      let first := scanMatch xs word
      let rest := scanMatch ys first.rest
      ⟨first.valid && rest.valid,rest.rest⟩ := by
  induction xs generalizing word with
  | nil => simp [scanMatch]
  | cons tok rest ih =>
    simp only [List.cons_append,scanMatch,ih,Bool.and_assoc]

def wordEffect (tokens : List Token) (s : Store) : Store :=
  let result := scanMatch tokens (s fr)
  (s.set fr result.rest).set gues (markedIf (s gues) (result.valid = true))

theorem wordEffect_append (xs ys : List Token) (s : Store) :
    wordEffect (xs++ys) s = wordEffect ys (wordEffect xs s) := by
  simp only [wordEffect,scanMatch_append]
  funext i
  by_cases a : i = fr <;> by_cases b : i = gues <;>
    simp [Store.set,a,b,fr,gues,markedIf_and,Bool.and_eq_true] <;> rfl

theorem wordEffect_dict (w : List Token) (s : Store) : wordEffect w s dc = s dc := by
  simp [wordEffect,Store.set,fr,gues,dc]

/-- A side contains literals and captures only. Its effect is the match
against the instantiated preorder tokens. -/
theorem side_match (is : List Instruction) (s : Store) (side : .reverse ∉ is) :
    FrontBounds
      (wordEffect (is.flatMap (substituteInstruction (Dictionary.decode (s dc)).capture)) s)
      (instructionsEffect is s) := by
  induction is generalizing s with
  | nil =>
    constructor <;> simp [instructionsEffect,wordEffect,scanMatch,Store.set,markedIf,fr,gues,dc,lv,np]
  | cons i rest ih =>
    have next := ih (instructionEffect i s) (fun bad => side (List.mem_cons_of_mem _ bad))
    have constant : instructionEffect i s dc = s dc := by
      cases i <;>
        simp [instructionEffect,literalEffect,captureEffect,Store.set,dc,fr,gues,goal,tmp,lv]
    have first : FrontBounds
        (wordEffect (substituteInstruction (Dictionary.decode (s dc)).capture i) s)
        (instructionEffect i s) := by
      cases i with
      | literal token => exact FrontBounds.refl _
      | reverse => exact (side List.mem_cons_self).elim
      | capture slot =>
        constructor <;>
          simp [instructionEffect,captureEffect,wordEffect,substituteInstruction,Store.set,
            gues,fr,lv,dc,np,tmp,goal] <;> rfl
    let restTokens := rest.flatMap (substituteInstruction (Dictionary.decode (s dc)).capture)
    have next' : FrontBounds (wordEffect restTokens (instructionEffect i s))
        (instructionsEffect rest (instructionEffect i s)) := by
      simpa only [constant,restTokens] using next
    have preserves (tokens : List Token) {a b : Store} (same : FrontBounds a b) :
        FrontBounds (wordEffect tokens a) (wordEffect tokens b) := by
      constructor <;> simp [wordEffect,Store.set,fr,lv,dc,np,gues,
        same.left,same.right,same.dictionary,same.marker,same.word,same.unused]
    have composed := (preserves restTokens first).trans next'
    simpa only [List.flatMap_cons,wordEffect_append,instructionsEffect,List.foldl_cons,restTokens] using composed

theorem instructions_no_reverse (p : Pattern) : .reverse ∉ p.instructions := by
  induction p <;> simp [Pattern.instructions, List.mem_append, *]

theorem pattern_match (p : Pattern) (s : Store) :
    FrontBounds (wordEffect (p.instantiate (Dictionary.decode (s dc)).capture).tokens s)
      (instructionsEffect p.instructions s) := by
  rw [p.instantiate_instructions]
  exact side_match p.instructions s (instructions_no_reverse p)

def frontsAccept (eqn : Templates.Equation) (dict : Dictionary) (old proposal : Nat) : Bool :=
  let first := scanMatch (eqn.1.instantiate dict.capture).tokens old
  let second := scanMatch (eqn.2.instantiate dict.capture).tokens proposal
  first.valid && second.valid && (first.rest == second.rest)

theorem frontsAccept_exact (eqn : Templates.Equation) (dict : Dictionary) (old proposal : Nat) :
    frontsAccept eqn dict old proposal =
      match matchTokens (eqn.1.instantiate dict.capture).tokens old,
          matchTokens (eqn.2.instantiate dict.capture).tokens proposal with
      | some x, some y => x == y
      | _, _ => false := by
  rw [scanMatch_exact,scanMatch_exact]
  unfold frontsAccept
  dsimp only
  cases (scanMatch (eqn.1.instantiate dict.capture).tokens old).valid <;>
    cases (scanMatch (eqn.2.instantiate dict.capture).tokens proposal).valid <;> rfl

/-- Read the first side, exchange the two numeric fronts, and compare
the second side. The updated marker still needs the residual equality. -/
theorem row_fronts (eqn : Templates.Equation) (s : Store) :
    let dict := Dictionary.decode (s dc)
    let a := scanMatch (eqn.1.instantiate dict.capture).tokens (s fr)
    let b := scanMatch (eqn.2.instantiate dict.capture).tokens (s lv)
    let out := instructionsEffect (equationInstructions eqn) s
    out lv = a.rest ∧ out fr = b.rest ∧
      out gues = markedIf (s gues) (a.valid = true ∧ b.valid = true) ∧ out dc = s dc ∧ out np = s np := by
  let dict := Dictionary.decode (s dc)
  let left := instructionsEffect eqn.1.instructions s
  let middle := (left.set fr (left lv)).set lv (left fr)
  have first := pattern_match eqn.1 s
  have right := pattern_match eqn.2 middle
  have leftResidual : left fr = (scanMatch (eqn.1.instantiate dict.capture).tokens (s fr)).rest := by
    simpa [left,dict,wordEffect,Store.set,fr,gues] using first.left
  have leftMark : left gues = markedIf (s gues)
      ((scanMatch (eqn.1.instantiate dict.capture).tokens (s fr)).valid = true) := by
    simpa [left,dict,wordEffect,Store.set,fr,gues] using first.marker
  have unchanged₁ : left lv = s lv := by simpa [left,wordEffect,Store.set,lv,fr,gues] using first.right
  have unchanged₂ : left dc = s dc := by simpa [left,wordEffect,Store.set,dc,fr,gues] using first.dictionary
  have unchanged₃ : left np = s np := by simpa [left,wordEffect,Store.set,np,fr,gues] using first.word
  simp only [equationInstructions, instructionsEffect, List.foldl_append, List.foldl_cons,
    instructionEffect]
  change instructionsEffect eqn.2.instructions middle lv = _ ∧
    instructionsEffect eqn.2.instructions middle fr = _ ∧
    instructionsEffect eqn.2.instructions middle gues = _ ∧
    instructionsEffect eqn.2.instructions middle dc = _ ∧
    instructionsEffect eqn.2.instructions middle np = _
  constructor
  · simpa [middle,wordEffect,Store.set,lv,fr,gues,leftResidual] using right.right
  constructor
  · simpa [middle,wordEffect,Store.set,lv,fr,gues,dc,unchanged₁,unchanged₂,dict] using right.left
  constructor
  · simpa [middle,wordEffect,Store.set,lv,fr,gues,dc,unchanged₁,unchanged₂,dict,leftMark,
      markedIf_and] using right.marker
  constructor
  · simpa [middle,wordEffect,Store.set,lv,fr,gues,dc,unchanged₂] using right.dictionary
  · simpa [middle,wordEffect,Store.set,lv,fr,gues,np,unchanged₃] using right.word

end PalomarI3334.SearchProgram
