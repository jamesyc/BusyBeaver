module
public import SearchCommands
@[expose] public section
namespace C207Search
open C207Soundness M6.Source.Cantor M6.Source.Enumeration

inductive SoundStack : Nat → Prop
 | zero : SoundStack 0
 | push {a w : Nat} : ExactProvable a → SoundStack w → SoundStack (pair a w)

theorem SoundStack.pop {w : Nat} (hw : SoundStack w) :
 ExactProvable (M6.Source.Cantor.decode w).1 ∧ SoundStack (M6.Source.Cantor.decode w).2 := by
 cases hw with
 | zero => exact ⟨proved_zero,.zero⟩
 | push ha hw => rw [decode_pair]; exact ⟨ha,hw⟩

theorem SoundStack.prepend (xs : List Nat) (w : Nat)
 (hx : ∀ a ∈ xs, ExactProvable a) (hw : SoundStack w) : SoundStack (xs.foldr pair w) := by
 induction xs with
 | nil => exact hw
 | cons a xs ih =>
   exact .push (hx a (by simp)) (ih (by intro x h; exact hx x (by simp [h])))

def SoundStore (s : CommandStore) : Prop := ExactProvable s.t ∧ ExactProvable s.h ∧ SoundStack s.w

theorem zero_sound : SoundStore zeroStore := ⟨proved_zero,proved_zero,.zero⟩

theorem gate_proved (a d h : Nat) : ExactProvable (gate a d h) := by
 unfold gate
 split
 · rename_i hg
   apply proved_axiom
   exact Or.inr ⟨a,d,h,0,by simp [hg.1,hg.2]⟩
 · exact proved_zero

theorem heads_proved (a d h oldd oldh : Nat) (hb : oldd ≤ d)
 (hh : ExactProvable oldh) : ∀ x ∈ heads a d h oldd oldh, ExactProvable x := by
 intro x hx
 simp only [heads,List.mem_cons,List.not_mem_nil,or_false] at hx
 rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 all_goals first
 | solve | exact proved_gen oldd hh
 | solve | exact proved_axiom (Or.inr ⟨a,d,h,oldd,by simp [hb]⟩)

/-- Safety includes the zero alias and arbitrary stack underflow. The numeric
working offset d is not required to contain a theorem. -/
theorem command_safe (hn : ¬ ExactProvable 1) (c : Command) (s : CommandStore)
 (hs : SoundStore s) : ∃ out, commandEval c s = some out ∧ SoundStore out := by
 obtain ⟨ht,hh,hw⟩ := hs
 cases c with
 | shift =>
   have hne : s.t+s.h ≠ 1 := by
    intro he
    have hc : s.t=1 ∨ s.h=1 := by omega
    rcases hc with hc | hc
    · exact hn (hc ▸ ht)
    · exact hn (hc ▸ hh)
   refine ⟨⟨s.h,(M6.Source.Cantor.decode s.w).2,s.d,(M6.Source.Cantor.decode s.w).1⟩,?_,hh,hw.pop.1,hw.pop.2⟩
   simp [commandEval,hne]
 | mp x =>
   by_cases he : impCode s.t (s.d+x)=s.h
   · have hv : ExactProvable (s.d+x) := proved_mp ht (he ▸ hh)
     refine ⟨⟨s.d+x,pair 0 s.w,s.d+x,0⟩,?_,hv,proved_zero,.push proved_zero hw⟩
     simp [commandEval,he]
   · refine ⟨⟨0,s.w,s.d+x,0⟩,?_,proved_zero,proved_zero,hw⟩
     simp [commandEval,he]
 | ax a x y =>
   refine ⟨_,rfl,gate_proved _ _ _,proved_zero,?_⟩
   apply SoundStack.prepend _ _ _ hw
   intro v hv
   rcases List.mem_append.mp hv with hv | hv
   · exact heads_proved a (s.d+x) (s.h+y) s.d s.h (by omega) hh v hv
   · exact (List.mem_singleton.mp hv) ▸ ht

theorem words_safe (hn : ¬ ExactProvable 1) (cs : List Command) (s : CommandStore)
 (hs : SoundStore s) : ∃ out, commandsEval cs s = some out ∧ SoundStore out := by
 induction cs generalizing s with
 | nil => exact ⟨s,rfl,hs⟩
 | cons c cs ih =>
   obtain ⟨mid,hm,hsm⟩ := command_safe hn c s hs
   obtain ⟨out,ho,hso⟩ := ih mid hsm
   exact ⟨out,by simp [commandsEval,hm,ho],hso⟩

end C207Search
