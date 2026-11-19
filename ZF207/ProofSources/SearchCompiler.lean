module
public import SearchMacros
@[expose] public section
namespace C207Search
open C207Soundness M6.Source.Cantor M6.Source.Enumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- A compiler may find false earlier than the requested conclusion. This is
success, not a failed state invariant. The underlying stack is arbitrary. -/
def Compilable (n : Nat) : Prop := ∃ cs : List Command, ∀ t w,
 abstractEval cs ⟨t,w,0,0⟩ = none ∨ abstractEval cs ⟨t,w,0,0⟩ = some ⟨n,w,0,0⟩

def GEN (i : Nat) : List Command :=
 PUSH ++ (J i ++ ([.shift] ++ ([.ax i 0 0] ++ List.replicate 9 .shift)))

theorem GEN_total (i a w : Nat) :
 commandsEval (GEN i) ⟨a,w,0,0⟩ = some ⟨allCode i a,w,0,0⟩ := by
 rw [GEN,commandsEval_append,PUSH_total]
 simp only [Option.bind_some]
 rw [commandsEval_append,J_total]
 simp only [Option.bind_some]
 rw [commandsEval_append]
 simp only [commandsEval,commandEval,Nat.zero_add,decode_pair,Option.bind_some,show (0:Nat) ≠ 1 by decide,ite_false]
 rw [AX_shift9]


def MPtail (b : Nat) : List Command :=
 [.shift,.shift,.mp b] ++ ([.ax b 0 0] ++ List.replicate 10 .shift)

theorem MPtail_result (a b w : Nat) :
 commandsEval (MPtail b) ⟨0,pair a (pair (impCode a b) w),0,0⟩ = none ∨
 commandsEval (MPtail b) ⟨0,pair a (pair (impCode a b) w),0,0⟩ = some ⟨b,w,0,0⟩ := by
 have hp : commandsEval [.shift,.shift,.mp b] ⟨0,pair a (pair (impCode a b) w),0,0⟩ =
   if a=1 then none else some ⟨b,pair 0 w,b,0⟩ := by
   by_cases ha : a=1 <;> simp [commandsEval,commandEval,decode_pair,ha]
 by_cases ha : a=1
 · left
   rw [MPtail,commandsEval_append,hp,if_pos ha]
   rfl
 · right
   rw [MPtail,commandsEval_append,hp,if_neg ha]
   simp only [Option.bind_some]
   rw [AX_shift10,decode_pair]


private theorem abstract_PUSH_total (t w d h : Nat) : abstractEval PUSH ⟨t,w,d,h⟩ = some ⟨0,pair t w,0,0⟩ := by
 rw [abstractEval_eq]; exact PUSH_total t w d h
private theorem abstract_GEN_total (i a w : Nat) : abstractEval (GEN i) ⟨a,w,0,0⟩ = some ⟨allCode i a,w,0,0⟩ := by
 rw [abstractEval_eq]; exact GEN_total i a w
private theorem abstract_MPtail_result (a b w : Nat) :
 abstractEval (MPtail b) ⟨0,pair a (pair (impCode a b) w),0,0⟩ = none ∨
 abstractEval (MPtail b) ⟨0,pair a (pair (impCode a b) w),0,0⟩ = some ⟨b,w,0,0⟩ := by
 simp only [abstractEval_eq]
 exact MPtail_result a b w
private theorem abstract_shift_halt (w : Nat) : abstractEval [.shift] ⟨1,w,0,0⟩ = none := by
 rw [abstractEval_eq]
 simp [commandsEval,commandEval]
theorem axiom_compilable {n : Nat} (h : ExactAxiom n) : Compilable n := by
 rcases h with rfl | ⟨a,d,h,u,hax⟩
 · exact ⟨DISCARD,fun t w => Or.inr (by rw [abstractEval_eq]; exact DISCARD_total t w)⟩
 · rcases hax with h1 | h2 | h3 | h4 | h5 | h6 | hr | hg
   · subst n; exact ⟨supplyHead 1 a d h,fun t w => Or.inr (by rw [abstractEval_eq]; exact supplyHead1_total a d h t w)⟩
   · subst n; exact ⟨supplyHead 2 a d h,fun t w => Or.inr (by rw [abstractEval_eq]; exact supplyHead2_total a d h t w)⟩
   · subst n; exact ⟨supplyHead 3 a d h,fun t w => Or.inr (by rw [abstractEval_eq]; exact supplyHead3_total a d h t w)⟩
   · subst n; exact ⟨supplyHead 4 a d h,fun t w => Or.inr (by rw [abstractEval_eq]; exact supplyHead4_total a d h t w)⟩
   · subst n; exact ⟨supplyHead 5 a d h,fun t w => Or.inr (by rw [abstractEval_eq]; exact supplyHead5_total a d h t w)⟩
   · subst n; exact ⟨supplyHead 6 a d h,fun t w => Or.inr (by rw [abstractEval_eq]; exact supplyHead6_total a d h t w)⟩
   · obtain ⟨hu,rfl⟩ := hr
     exact ⟨supplyRho a d h u,fun t w => Or.inr (by rw [abstractEval_eq]; exact supplyRho_total a d h u t w hu)⟩
   · obtain ⟨had,hah,rfl⟩ := hg
     refine ⟨supplyGate a d h,?_⟩
     intro t w
     right
     rw [abstractEval_eq]
     have he : gate a d h = pointedGateCode a d h := if_pos ⟨had,hah⟩
     have hs := supplyGate_total a d h t w
     rw [he] at hs
     exact hs

theorem gen_compilable (i : Nat) {a : Nat} (h : Compilable a) : Compilable (allCode i a) := by
 obtain ⟨cs,hcs⟩ := h
 refine ⟨cs ++ GEN i,?_⟩
 intro t w
 rcases hcs t w with hh | hr
 · left; rw [abstractEval_append,hh]; rfl
 · right; rw [abstractEval_append,hr]; exact abstract_GEN_total i a w

theorem mp_compilable {a b : Nat} (ha : Compilable a) (hi : Compilable (impCode a b)) : Compilable b := by
 obtain ⟨cs,hcs⟩ := hi
 obtain ⟨ds,hds⟩ := ha
 refine ⟨cs ++ (PUSH ++ (ds ++ (PUSH ++ MPtail b))),?_⟩
 intro t w
 rcases hcs t w with hh | hr
 · left; rw [abstractEval_append,hh]; rfl
 · simp only [abstractEval_append,hr,Option.bind_some,abstract_PUSH_total]
   rcases hds 0 (pair (impCode a b) w) with hh | hr
   · left; rw [hh]; rfl
   · rw [hr]
     simp only [Option.bind_some,abstractEval_append,abstract_PUSH_total]
     exact abstract_MPtail_result a b w

theorem derivation_compilable {n : Nat} (h : Derivable n) : Compilable n := by
 induction h with
 | ax h => exact axiom_compilable h
 | mp _ _ iha ihi => exact mp_compilable iha ihi
 | gen i _ ih => exact gen_compilable i ih


/-- A single AX-first word halts from every command store, including retained
nonzero caches from earlier candidates. PUSH normalizes the arbitrary store. -/
theorem refutation_has_uniform_ax_word (h : ExactProvable 1) :
 ∃ cs : List Command, ∀ s : CommandStore,
   commandsEval (.ax 0 0 0 :: cs) s = none := by
 obtain ⟨cs,hcs⟩ := derivation_compilable ((derivable_iff_provable 1).mpr h)
 refine ⟨List.replicate 8 .shift ++ [.mp 0] ++ (cs ++ [.shift]),?_⟩
 intro s
 rw [← abstractEval_eq]
 have he : (Command.ax 0 0 0 :: (List.replicate 8 .shift ++ [.mp 0] ++ (cs ++ [.shift]))) =
   PUSH ++ (cs ++ [.shift]) := by simp [PUSH,List.append_assoc]
 rw [he]
 obtain ⟨t,w,d,h⟩ := s
 rw [abstractEval_append,abstract_PUSH_total]
 simp only [Option.bind_some]
 rcases hcs 0 (pair t w) with hh | hr
 · rw [abstractEval_append,hh]; rfl
 · rw [abstractEval_append,hr]
   simp only [Option.bind_some]
   exact abstract_shift_halt (pair t w)

end C207Search
