module
public import DirectOpcodeDispatch
@[expose] public section
namespace RosserDirect.Routine
open Turing
variable {K J L Q A V : Type} [DecidableEq K] [DecidableEq J]

/-- Structural relocation of finite routine code into a larger interpreter.
Only stack names and control labels change. Runtime functions are untouched. -/
def relocate (roles : K → J) (labels : L → Q) :
 TM2.Stmt (fun _ : K => A) L V → TM2.Stmt (fun _ : J => A) Q V
 | .push k f s => .push (roles k) f (relocate roles labels s)
 | .peek k f s => .peek (roles k) f (relocate roles labels s)
 | .pop k f s => .pop (roles k) f (relocate roles labels s)
 | .load f s => .load f (relocate roles labels s)
 | .branch f s t => .branch f (relocate roles labels s) (relocate roles labels t)
 | .goto f => .goto (fun v => labels (f v))
 | .halt => .halt

def Related (roles : K → J) (labels : L → Q)
    (c : TM2.Cfg (fun _ : K => A) L V) (d : TM2.Cfg (fun _ : J => A) Q V) : Prop :=
 d.l = c.l.map labels ∧ d.var = c.var ∧ (fun k => d.stk (roles k)) = c.stk

theorem project_update (roles : K → J) (hi : Function.Injective roles)
    (S : J → List A) (k : K) (xs : List A) :
 (fun j => Function.update S (roles k) xs (roles j)) =
 Function.update (fun j => S (roles j)) k xs := by
 funext j
 by_cases h : j = k
 · subst j; simp
 · have hn : roles j ≠ roles k := fun he => h (hi he)
   simp [Function.update_of_ne h,Function.update_of_ne hn]

theorem relocate_correct (roles : K → J) (hi : Function.Injective roles) (labels : L → Q)
    (s : TM2.Stmt (fun _ : K => A) L V) (v : V)
    (S : K → List A) (T : J → List A) (h : (fun k => T (roles k)) = S) :
 Related roles labels (TM2.stepAux s v S) (TM2.stepAux (relocate roles labels s) v T) := by
 induction s generalizing v S T with
 | push k f s ih =>
   simp only [relocate,TM2.stepAux]
   apply ih
   rw [project_update roles hi,h,congrFun h k]
 | peek k f s ih =>
   simp only [relocate,TM2.stepAux]
   have hk := congrFun h k
   rw [hk]
   exact ih _ _ _ h
 | pop k f s ih =>
   simp only [relocate,TM2.stepAux]
   have hk := congrFun h k
   rw [hk]
   apply ih
   rw [project_update roles hi,h]
 | load f s ih => exact ih _ _ _ h
 | branch f s t is it =>
   simp only [relocate,TM2.stepAux]
   cases f v
   · exact it _ _ _ h
   · exact is _ _ _ h
 | goto f => exact ⟨rfl,rfl,h⟩
 | halt => exact ⟨rfl,rfl,h⟩

/-- Relocated routines cannot modify any stack outside their assigned roles. -/
theorem untouched (roles : K → J) (labels : L → Q)
    (s : TM2.Stmt (fun _ : K => A) L V) (j : J) (hj : ∀ k, j ≠ roles k)
    (v : V) (T : J → List A) :
 (TM2.stepAux (relocate roles labels s) v T).stk j = T j := by
 induction s generalizing v T with
 | push k f s ih =>
   simp only [relocate,TM2.stepAux]
   rw [ih,Function.update_of_ne (hj k)]
 | peek k f s ih => exact ih _ _
 | pop k f s ih =>
   simp only [relocate,TM2.stepAux]
   rw [ih,Function.update_of_ne (hj k)]
 | load f s ih => exact ih _ _
 | branch f s t is it =>
   simp only [relocate,TM2.stepAux]
   cases f v
   · exact it _ _
   · exact is _ _
 | goto f => rfl
 | halt => rfl

/-- One live local step embeds into the ambient interpreter. Terminal routine
labels may be wired to continuations because no agreement is needed for halt. -/
theorem lift_live_step (roles : K → J) (hi : Function.Injective roles) (labels : L → Q)
    (M : L → TM2.Stmt (fun _ : K => A) L V)
    (N : Q → TM2.Stmt (fun _ : J => A) Q V)
    (agree : ∀ q, M q ≠ .halt → N (labels q) = relocate roles labels (M q))
    {c c' : TM2.Cfg (fun _ : K => A) L V} {d : TM2.Cfg (fun _ : J => A) Q V}
    (rel : Related roles labels c d) (step : TM2.step M c = some c') (live : c'.l ≠ none) :
 ∃ d', TM2.step N d = some d' ∧ Related roles labels c' d' ∧
   ∀ j, (∀ k, j ≠ roles k) → d'.stk j = d.stk j := by
 rcases c with ⟨l,v,S⟩
 cases l with
 | none => simp [TM2.step] at step
 | some q =>
   have hs : c' = TM2.stepAux (M q) v S := by simpa [TM2.step] using step.symm
   subst c'
   have hn : M q ≠ .halt := by intro he; apply live; simp [he,TM2.stepAux]
   rcases d with ⟨l',v',T⟩
   rcases rel with ⟨hl,hv,ht⟩
   change l' = some (labels q) at hl
   change v' = v at hv
   subst l'; subst v'
   refine ⟨TM2.stepAux (relocate roles labels (M q)) v T, ?_, ?_, ?_⟩
   · simp only [TM2.step,agree q hn]
   · exact relocate_correct roles hi labels (M q) v S T ht
   · intro j hj; exact untouched roles labels (M q) j hj v T



theorem dead_reaches (M : L → TM2.Stmt (fun _ : K => A) L V)
    {c c' : TM2.Cfg (fun _ : K => A) L V} (dead : c.l = none)
    (h : TM2.Reaches M c c') : c' = c := by
 induction h with
 | refl => rfl
 | tail h hs ih =>
   rw [ih] at hs
   have hz : TM2.step M c = none := by cases c; simp_all [TM2.step]
   simp [hz] at hs

theorem source_live (M : L → TM2.Stmt (fun _ : K => A) L V)
    {c c' : TM2.Cfg (fun _ : K => A) L V}
    (h : TM2.Reaches M c c') (live : c'.l ≠ none) : c.l ≠ none := by
 intro hd
 have he := dead_reaches M hd h
 exact live (he ▸ hd)

/-- A complete verified local run can be embedded in an ambient interpreter.
Local terminal labels can execute caller continuations; the proof stops before
executing that final label. All unrelated stacks are preserved. -/
theorem lift_run (roles : K → J) (hi : Function.Injective roles) (labels : L → Q)
    (M : L → TM2.Stmt (fun _ : K => A) L V)
    (N : Q → TM2.Stmt (fun _ : J => A) Q V)
    (agree : ∀ q, M q ≠ .halt → N (labels q) = relocate roles labels (M q))
    {c c' : TM2.Cfg (fun _ : K => A) L V} {d : TM2.Cfg (fun _ : J => A) Q V}
    (trace : TM2.Reaches M c c') (live : c'.l ≠ none) (rel : Related roles labels c d) :
 ∃ d', TM2.Reaches N d d' ∧ Related roles labels c' d' ∧
   ∀ j, (∀ k, j ≠ roles k) → d'.stk j = d.stk j := by
 induction trace generalizing d with
 | refl => exact ⟨d,Relation.ReflTransGen.refl,rel,fun _ _ => rfl⟩
 | @tail mid last h hs ih =>
   have hl : mid.l ≠ none := source_live M (Relation.ReflTransGen.single hs) live
   obtain ⟨dm,hm,rm,em⟩ := ih hl rel
   obtain ⟨dl,hl,rl,el⟩ := lift_live_step roles hi labels M N agree rm hs live
   refine ⟨dl,hm.trans (Relation.ReflTransGen.single hl),rl,?_⟩
   intro j hj
   rw [el j hj,em j hj]



/-- Choice-free installation for the existing three-stack routines. -/
def install (roles : Stack → J) (S : Stack → List A) (extra : J → List A) : J → List A :=
 fun j => if j = roles .input then S .input else
   if j = roles .scratch then S .scratch else if j = roles .output then S .output else extra j

theorem install_project (roles : Stack → J) (hi : Function.Injective roles)
    (S : Stack → List A) (extra : J → List A) :
 (fun k => install roles S extra (roles k)) = S := by
 funext k
 have he (a b : Stack) : roles a = roles b ↔ a = b := ⟨fun h => hi h,congrArg roles⟩
 cases k <;> simp [install,he]

theorem install_extra (roles : Stack → J) (S : Stack → List A) (extra : J → List A)
    (j : J) (hj : ∀ k, j ≠ roles k) : install roles S extra j = extra j := by
 simp [install,hj]

def embed (roles : Stack → J) (labels : L → Q)
    (c : TM2.Cfg (fun _ : Stack => A) L V) (extra : J → List A) :
    TM2.Cfg (fun _ : J => A) Q V :=
 ⟨c.l.map labels,c.var,install roles c.stk extra⟩

theorem embed_related (roles : Stack → J) (hi : Function.Injective roles) (labels : L → Q)
    (c : TM2.Cfg (fun _ : Stack => A) L V) (extra : J → List A) :
 Related roles labels c (embed roles labels c extra) :=
 ⟨rfl,rfl,install_project roles hi c.stk extra⟩

theorem reconstruct (roles : Stack → J) (labels : L → Q)
    (c : TM2.Cfg (fun _ : Stack => A) L V) (d : TM2.Cfg (fun _ : J => A) Q V)
    (extra : J → List A) (hr : Related roles labels c d)
    (he : ∀ j, (∀ k, j ≠ roles k) → d.stk j = extra j) :
 d = embed roles labels c extra := by
 rcases c with ⟨l,v,S⟩
 rcases d with ⟨l',v',T⟩
 rcases hr with ⟨hl,hv,ht⟩
 change l' = l.map labels at hl
 change v' = v at hv
 subst l'; subst v'
 congr 1
 funext j
 by_cases h0 : j = roles .input
 · subst j; simpa [install] using congrFun ht .input
 by_cases h1 : j = roles .scratch
 · subst j; simpa [install,h0] using congrFun ht .scratch
 by_cases h2 : j = roles .output
 · subst j; simpa [install,h0,h1] using congrFun ht .output
 have hn : ∀ k, j ≠ roles k := by intro k; cases k <;> assumption
 simpa [install,h0,h1,h2] using he j hn

theorem lift_embedded_run (roles : Stack → J) (hi : Function.Injective roles) (labels : L → Q)
    (M : L → TM2.Stmt (fun _ : Stack => A) L V)
    (N : Q → TM2.Stmt (fun _ : J => A) Q V)
    (agree : ∀ q, M q ≠ .halt → N (labels q) = relocate roles labels (M q))
    {c c' : TM2.Cfg (fun _ : Stack => A) L V} (extra : J → List A)
    (trace : TM2.Reaches M c c') (live : c'.l ≠ none) :
 TM2.Reaches N (embed roles labels c extra) (embed roles labels c' extra) := by
 obtain ⟨d,hd,hr,he⟩ := lift_run roles hi labels M N agree trace live (embed_related roles hi labels c extra)
 have he' : ∀ j, (∀ k, j ≠ roles k) → d.stk j = extra j := by
   intro j hj
   rw [he j hj]
   exact install_extra roles c.stk extra j hj
 rw [reconstruct roles labels c' d extra hr he'] at hd
 exact hd

end RosserDirect.Routine
