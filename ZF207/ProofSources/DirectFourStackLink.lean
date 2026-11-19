module
public import DirectFourStack
@[expose] public section
namespace RosserDirect.FourStack
open Turing
variable {J L Q : Type} [DecidableEq J]

def install4 (roles : K → J) (S : K → List Symbol) (extra : J → List Symbol) : J → List Symbol :=
 fun j => if j = roles .stream then S .stream else
   if j = roles .data then S .data else if j = roles .scratch then S .scratch else
   if j = roles .output then S .output else extra j

theorem install4_project (roles : K → J) (hi : Function.Injective roles)
 (S : K → List Symbol) (extra : J → List Symbol) :
 (fun k => install4 roles S extra (roles k)) = S := by
 funext k
 have he (a b : K) : roles a = roles b ↔ a = b := ⟨fun h => hi h,congrArg roles⟩
 cases k <;> simp [install4,he]

theorem install4_extra (roles : K → J) (S : K → List Symbol) (extra : J → List Symbol)
 (j : J) (hj : ∀ k, j ≠ roles k) : install4 roles S extra j = extra j := by
 simp [install4,hj]

def embed4 (roles : K → J) (labels : L → Q) (c : Cfg4 L) (extra : J → List Symbol) :
 TM2.Cfg (fun _ : J => Symbol) Q (Option Symbol) :=
 ⟨c.l.map labels,c.var,install4 roles c.stk extra⟩

theorem embed4_related (roles : K → J) (hi : Function.Injective roles) (labels : L → Q)
 (c : Cfg4 L) (extra : J → List Symbol) : Routine.Related roles labels c (embed4 roles labels c extra) :=
 ⟨rfl,rfl,install4_project roles hi c.stk extra⟩

theorem reconstruct4 (roles : K → J) (labels : L → Q)
 (c : Cfg4 L) (d : TM2.Cfg (fun _ : J => Symbol) Q (Option Symbol))
 (extra : J → List Symbol) (hr : Routine.Related roles labels c d)
 (he : ∀ j, (∀ k, j ≠ roles k) → d.stk j = extra j) : d = embed4 roles labels c extra := by
 rcases c with ⟨l,v,S⟩
 rcases d with ⟨l',v',T⟩
 rcases hr with ⟨hl,hv,ht⟩
 change l' = l.map labels at hl
 change v' = v at hv
 subst l'; subst v'
 congr 1
 funext j
 by_cases h0 : j = roles .stream
 · subst j; simpa [install4] using congrFun ht .stream
 by_cases h1 : j = roles .data
 · subst j; simpa [install4,h0] using congrFun ht .data
 by_cases h2 : j = roles .scratch
 · subst j; simpa [install4,h0,h1] using congrFun ht .scratch
 by_cases h3 : j = roles .output
 · subst j; simpa [install4,h0,h1,h2] using congrFun ht .output
 have hn : ∀ k, j ≠ roles k := by intro k; cases k <;> assumption
 simpa [install4,h0,h1,h2,h3] using he j hn

/-- Embed a verified four-stack quantifier routine into the five-stack checker.
All stacks outside the injective role assignment remain exactly unchanged. -/
theorem lift4_run (roles : K → J) (hi : Function.Injective roles) (labels : L → Q)
 (M : L → Stmt4 L) (N : Q → TM2.Stmt (fun _ : J => Symbol) Q (Option Symbol))
 (agree : ∀ q, M q ≠ .halt → N (labels q) = Routine.relocate roles labels (M q))
 {c c' : Cfg4 L} (extra : J → List Symbol)
 (trace : TM2.Reaches M c c') (live : c'.l ≠ none) :
 TM2.Reaches N (embed4 roles labels c extra) (embed4 roles labels c' extra) := by
 obtain ⟨d,hd,hr,he⟩ := Routine.lift_run roles hi labels M N agree trace live (embed4_related roles hi labels c extra)
 have he' : ∀ j, (∀ k, j ≠ roles k) → d.stk j = extra j := by
   intro j hj
   rw [he j hj]
   exact install4_extra roles c.stk extra j hj
 rw [reconstruct4 roles labels c' d extra hr he'] at hd
 exact hd

end RosserDirect.FourStack
