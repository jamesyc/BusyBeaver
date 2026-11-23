module
public import I3_334.Search.TrieCompleteness
public import I3_334.Search.SearchSoundness
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open Templates (equations equationInstructions Guarded)

def rowValues (word : Nat) : Fin 4 → RawTerm := (Dictionary.decode word).capture

def recodeDictionary (word tail : Nat) : Dictionary :=
  { Dictionary.ofTerms (rowValues word) with a := writeRaw 0 (rowValues word 0).tokens tail }

theorem recoded_capture (word tail : Nat) :
    (recodeDictionary word tail).capture = rowValues word ∧
      (scanRaw 0 (recodeDictionary word tail).a 1).2 = tail :=
  Dictionary.capture_withTail (rowValues word) (Dictionary.capture_guarded _) tail

def encodeHeader (e : Templates.Equation) (reverse : Bool)
    (position dictionary proposal tail : Nat) : TrialHeader :=
  let steps := rowRecipe (equationInstructions e)
  ⟨proposal,2*position+reverse.toNat,(recodeDictionary dictionary (tailChoice steps)).encode,
    selectors steps tail⟩

theorem encoded_header_position (e : Templates.Equation) (reverse : Bool)
    (position dictionary proposal tail : Nat) :
    (encodeHeader e reverse position dictionary proposal tail).position = position := by
  cases reverse <;> simp [encodeHeader,TrialHeader.position] <;> omega

theorem encoded_header_reverse (e : Templates.Equation) (reverse : Bool)
    (position dictionary proposal tail : Nat) :
    (encodeHeader e reverse position dictionary proposal tail).reverse = reverse := by
  have normal : (2*position+reverse.toNat)%2 = reverse.toNat := by
    cases reverse <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
  simp only [encodeHeader,TrialHeader.reverse,normal]
  cases reverse <;> rfl

theorem encoded_mark (e : Templates.Equation) (reverse : Bool)
    (position dictionary before proposal tail : Nat)
    (accepts : checkTrial e reverse position dictionary before proposal = true) :
    (encodeHeader e reverse position dictionary proposal tail).mark e before = proposal := by
  let h := encodeHeader e reverse position dictionary proposal tail
  have decoded :
      (Dictionary.decode h.dictionary).capture = (Dictionary.decode dictionary).capture := by
    change (Dictionary.decode (recodeDictionary dictionary (tailChoice (rowRecipe (equationInstructions e)))).encode).capture = _
    rw [Dictionary.decode_encode]
    exact (recoded_capture _ _).1
  have agrees : h.check e before = true := by
    unfold TrialHeader.check
    rw [encoded_header_position,encoded_header_reverse]
    simp only [checkTrial,decoded]
    exact accepts
  simp only [TrialHeader.mark,show (encodeHeader e reverse position dictionary proposal tail).proposal = proposal from rfl,
    show (encodeHeader e reverse position dictionary proposal tail).check e before = true from agrees,
    markedIf,↓reduceIte]

/-- With the prepared proof number, the compiled trial picks the requested
equation, consumes exactly the encoded fields, and preserves the proof suffix. -/
theorem run_encoded_trial (s : Scheduler) (e : Templates.Equation) (member : e ∈ equations)
    (reverse : Bool) (position dictionary before proposal tail : Nat)
    (accepts : checkTrial e reverse position dictionary before proposal = true)
    (pending : s.begin.pending = (encodeHeader e reverse position dictionary proposal tail).encode)
    (current : s.begin.incumbent = before) :
    ∃ scratchWord, Executes main s.store (trialFlow proposal) (s.finish tail proposal scratchWord).store := by
  let h := encodeHeader e reverse position dictionary proposal tail
  let line := equationInstructions e
  let steps := rowRecipe line
  let dict := recodeDictionary dictionary (tailChoice steps)
  let start := TrieInput s.begin h
  have declared : line ∈ templateTable := List.mem_map.mpr ⟨e,member,rfl⟩
  obtain ⟨recipe,emits,wellFormed⟩ := rowRecipe_ok line declared
  have codes : start dc = dict.encode := by simp [start,TrieInput,h,encodeHeader,dict,line,steps,Store.set,dc,gues]
  have words : start pl = selectors steps tail := by
    simp [start,TrieInput,h,encodeHeader,steps,line,Store.set,pl,fr,lv,dc,gues]
  have counter : start goal = 0 := by
    simp [start,TrieInput,Scheduler.store,Store.set,np,pl,fr,lv,dc,gues,goal,tmp]
  have residue : (scanRaw 0 dict.a 1).2 = tailChoice steps := (recoded_capture _ _).2
  obtain ⟨final,replay,suffix⟩ := run_encoded_recipe steps (tailChoice steps) tail dict
    wellFormed residue counter words codes
  have scratch := TrieInput.scratch s.begin h
  have instructions := recipe_runs templateFuel templateTable line recipe scratch replay
  have observed := runRecipe_observes replay
  rw [show emitted steps = line from emits] at observed
  have header : TrialHeader.decode s.begin.pending = h := by rw [pending,TrialHeader.decode_encode]
  have finishes := finish_trial s e final (by simpa only [header,rows,templateFuel,templateTable] using instructions)
    (runRecipe_clean replay scratch) (by simpa only [header] using observed)
  have mark : h.mark e s.begin.incumbent = proposal := by
    rw [current]
    exact encoded_mark e reverse position dictionary before proposal tail accepts
  exact ⟨final tmp, by simpa only [header,mark,suffix] using finishes⟩

private theorem prefix_right_zero {n left x y : Nat}
    (h : comparePrefix n left 0 = some (x,y)) : y = 0 := by
  induction n generalizing left x y with
  | zero =>
    have eq := Option.some.inj h
    exact (congrArg Prod.snd eq).symm
  | succ n ih =>
    rw [comparePrefix] at h
    split at h
    · rw [rawFields_zero] at h
      exact ih h
    · contradiction

theorem checkTrial_positive {e : Templates.Equation} {reverse : Bool}
    {position dictionary before proposal : Nat}
    (accepted : checkTrial e reverse position dictionary before proposal = true) : 0 < proposal := by
  by_contra notPositive
  have zero : proposal = 0 := by omega
  subst proposal
  unfold checkTrial acceptMatched at accepted
  cases prefixRun : comparePrefix position before 0 with
  | none => simp [prefixRun] at accepted
  | some fronts =>
    obtain ⟨x,y⟩ := fronts
    have empty := prefix_right_zero prefixRun
    simp [prefixRun,empty,RawTerm.match_empty] at accepted

end PalomarI3334.SearchProgram
