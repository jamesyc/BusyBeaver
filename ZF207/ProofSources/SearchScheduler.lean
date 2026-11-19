module
public import SearchEnumeration
@[expose] public section
namespace C207Search
open C207Soundness M6.Source.Enumeration

/-- Retained-store abstract sequential scheduler. Successful candidates pass
their ENTIRE returned store to the next candidate; there is no reset. Primitive
source implementation of this scheduler remains a distinct obligation. -/
def searchRun : Nat → Nat → CommandStore → Bool
 | 0,_,_ => false
 | fuel+1,n,s => match commandsEval (word n) s with
    | none => true
    | some out => searchRun fuel (n+1) out

def SequentialSearchHalts (first : Nat) (s : CommandStore) : Prop :=
 ∃ fuel, searchRun fuel first s = true

def UniformCandidateHalts (n : Nat) : Prop :=
 ∀ s, commandsEval (word n) s = none

theorem searchRun_safe (hn : ¬ ExactProvable 1) (fuel first : Nat) (s : CommandStore)
 (hs : SoundStore s) : searchRun fuel first s = false := by
 induction fuel generalizing first s with
 | zero => rfl
 | succ fuel ih =>
   obtain ⟨out,ho,hso⟩ := words_safe hn (word first) s hs
   simpa [searchRun,ho] using ih (first+1) out hso

theorem sequential_search_refutes (first : Nat) (s : CommandStore) (hs : SoundStore s)
 (h : SequentialSearchHalts first s) : ExactProvable 1 := by
 apply Classical.byContradiction
 intro hn
 obtain ⟨fuel,hf⟩ := h
 have he := searchRun_safe hn fuel first s hs
 rw [he] at hf
 cases hf

/-- A uniform halting candidate is eventually reached or an earlier candidate
already halts. No assumption is made about stores returned by earlier tests. -/
theorem searchRun_complete (first offset : Nat) (h : UniformCandidateHalts (first+offset)) :
 ∀ s, searchRun (offset+1) first s = true := by
 induction offset generalizing first with
 | zero =>
   intro s
   have hs : commandsEval (word first) s = none := by simpa using h s
   simp [searchRun,hs]
 | succ k ih =>
   intro s
   cases he : commandsEval (word first) s with
   | none => simp [searchRun,he]
   | some out =>
     have ht : UniformCandidateHalts ((first+1)+k) := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
     simpa [searchRun,he] using ih (first+1) ht out

theorem uniform_candidate_eventually (first n : Nat) (hn : first ≤ n)
 (h : UniformCandidateHalts n) (s : CommandStore) : SequentialSearchHalts first s := by
 refine ⟨n-first+1,?_⟩
 apply searchRun_complete first (n-first)
 simpa [Nat.add_sub_of_le hn] using h

theorem uniform_ax_word_search (a x y : Nat) (cs : List Command)
 (h : ∀ s, commandsEval (.ax a x y :: cs) s = none) (s : CommandStore) :
 SequentialSearchHalts 2 s := by
 apply uniform_candidate_eventually 2 (encodeWord (.ax a x y :: cs) 0-1)
 · exact ax_word_candidate_bound a x y cs
 · intro state
   rw [word_candidate]
   simpa [residual] using h state

end C207Search
