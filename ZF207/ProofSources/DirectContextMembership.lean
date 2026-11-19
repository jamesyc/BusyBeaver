module
public import DirectEncodingInjective
public import BottomUpND
@[expose] public section
namespace RosserDirect.Membership
open Turing
set_option backward.isDefEq.respectTransparency false

inductive Control where
 | next | scan | drop | restoreNext | restoreFound | found | absent | reject
 deriving DecidableEq, Fintype, Inhabited
abbrev Stmt := TM2.Stmt (fun _ : Stack => Symbol) Control (Option Symbol)
def cfg (q : Control) (v : Option Symbol) (a s c : List Symbol) :=
 (⟨some q, v, storage a s c⟩ : TM2.Cfg (fun _ : Stack => Symbol) Control (Option Symbol))

def restore (again done : Control) : Stmt :=
 .pop .scratch (fun _ x => x)
  (.branch Option.isNone (.goto (fun _ => done))
   (.push .input (fun x => x.getD .bit0) (.goto (fun _ => again))))

/-- Finite context lookup. Input holds the target frame, output holds successive
context frames. Scratch is used only to restore the target after each comparison.
No context or formula is stored in the finite register or control labels. -/
def machine : Control → Stmt
 | .next => .pop .output (fun _ x => x)
   (.branch Option.isNone (.goto (fun _ => .absent))
     (.push .output (fun x => x.getD .bit0) (.goto (fun _ => .scan))))
 | .scan => .pop .input (fun _ x => x)
   (.branch Option.isNone (.goto (fun _ => .reject))
    (.push .scratch (fun x => x.getD .bit0)
     (.pop .output (fun x y =>
        if y.isNone then none else
        if x == y then (if y == some .frameEnd then some .frameEnd else some .bit1)
        else (if y == some .frameEnd then some .tokenEnd else some .bit0))
      (.branch Option.isNone (.goto (fun _ => .reject))
       (.branch (fun x => x == some .frameEnd) (.goto (fun _ => .restoreFound))
        (.branch (fun x => x == some .bit1) (.goto (fun _ => .scan))
         (.branch (fun x => x == some .tokenEnd) (.goto (fun _ => .restoreNext))
          (.goto (fun _ => .drop)))))))))
 | .drop => .pop .output (fun _ x => x)
   (.branch Option.isNone (.goto (fun _ => .reject))
    (.branch (fun x => x == some .frameEnd)
     (.goto (fun _ => .restoreNext)) (.goto (fun _ => .drop))))
 | .restoreNext => restore .restoreNext .next
 | .restoreFound => restore .restoreFound .found
 | .found | .absent | .reject => .halt

theorem scan_same (x : Symbol) (hx : x ≠ .frameEnd) (v : Option Symbol)
    (a s c : List Symbol) :
 TM2.step machine (cfg .scan v (x :: a) s (x :: c)) =
 some (cfg .scan (some .bit1) a (x :: s) c) := by
 cases x <;> simp_all [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update]
 all_goals funext k; cases k <;> rfl

theorem scan_end (v : Option Symbol) (a s c : List Symbol) :
 TM2.step machine (cfg .scan v (.frameEnd :: a) s (.frameEnd :: c)) =
 some (cfg .restoreFound (some .frameEnd) a (.frameEnd :: s) c) := by
 simp [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update]
 funext k; cases k <;> rfl

theorem scan_mismatch (x y : Symbol) (h : x ≠ y) (v : Option Symbol)
    (a s c : List Symbol) :
 TM2.step machine (cfg .scan v (x :: a) s (y :: c)) =
 some (cfg (if y = .frameEnd then .restoreNext else .drop)
    (some (if y = .frameEnd then .tokenEnd else .bit0)) a (x :: s) c) := by
 cases x <;> cases y <;>
 simp_all [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update]
 all_goals funext k; cases k <;> rfl

theorem drop_step (x : Symbol) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step machine (cfg .drop v a s (x :: c)) =
 some (cfg (if x = .frameEnd then .restoreNext else .drop) (some x) a s c) := by
 cases x <;> simp [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update]
 all_goals funext k; cases k <;> rfl

theorem restore_step (found : Bool) (x : Symbol) (v : Option Symbol)
    (a s c : List Symbol) :
 TM2.step machine (cfg (if found then .restoreFound else .restoreNext) v a (x :: s) c) =
 some (cfg (if found then .restoreFound else .restoreNext) (some x) (x :: a) s c) := by
 cases found <;> cases x <;> simp [machine, restore, cfg, storage, TM2.step, TM2.stepAux, Function.update]
 all_goals funext k; cases k <;> rfl

theorem restore_empty (found : Bool) (v : Option Symbol) (a c : List Symbol) :
 TM2.step machine (cfg (if found then .restoreFound else .restoreNext) v a [] c) =
 some (cfg (if found then .found else .next) none a [] c) := by
 cases found <;> simp [machine, restore, cfg, storage, TM2.step, TM2.stepAux, Function.update]

theorem restore_all (found : Bool) (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches machine (cfg (if found then .restoreFound else .restoreNext) v a s c)
  (cfg (if found then .found else .next) none (s.reverse ++ a) [] c) := by
 induction s generalizing v a with
 | nil => exact Relation.ReflTransGen.single (by rw [restore_empty]; rfl)
 | cons x xs ih =>
   have one : TM2.Reaches machine
     (cfg (if found then .restoreFound else .restoreNext) v a (x :: xs) c)
     (cfg (if found then .restoreFound else .restoreNext) (some x) (x :: a) xs c) :=
     Relation.ReflTransGen.single (by rw [restore_step]; rfl)
   exact one.trans (by simpa [TM2.Reaches, List.reverse_cons, List.append_assoc] using ih (some x) (x :: a))

theorem drop_frame (p : List Symbol) (valid : ∀ x ∈ p, x ≠ .frameEnd)
    (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches machine (cfg .drop v a s (p ++ .frameEnd :: c))
  (cfg .restoreNext (some .frameEnd) a s c) := by
 induction p generalizing v with
 | nil => exact Relation.ReflTransGen.single (by rw [List.nil_append, drop_step]; rfl)
 | cons x xs ih =>
   have one : TM2.Reaches machine (cfg .drop v a s ((x :: xs) ++ .frameEnd :: c))
     (cfg .drop (some x) a s (xs ++ .frameEnd :: c)) :=
     Relation.ReflTransGen.single (by rw [List.cons_append, drop_step]; simp [valid x (by simp)])
   exact one.trans (ih (by intro y hy; exact valid y (by simp [hy])) _)



theorem mismatch_drop (x y : Symbol) (hne : x ≠ y) (hy : y ≠ .frameEnd)
    (q : List Symbol) (valid : ∀ z ∈ q, z ≠ .frameEnd)
    (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches machine (cfg .scan v (x :: a) s (y :: (q ++ .frameEnd :: c)))
  (cfg .next none (s.reverse ++ x :: a) [] c) := by
 have one : TM2.Reaches machine
   (cfg .scan v (x :: a) s (y :: (q ++ .frameEnd :: c)))
   (cfg .drop (some .bit0) a (x :: s) (q ++ .frameEnd :: c)) :=
   Relation.ReflTransGen.single (by rw [scan_mismatch x y hne]; simp [hy])
 have h := one.trans ((drop_frame q valid _ a (x :: s) c).trans
   (restore_all false (some .frameEnd) a (x :: s) c))
 simpa [TM2.Reaches, List.reverse_cons, List.append_assoc] using h

theorem scan_frames (p q : List Symbol)
    (vp : ∀ x ∈ p, x ≠ .frameEnd) (vq : ∀ x ∈ q, x ≠ .frameEnd)
    (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches machine (cfg .scan v (p ++ .frameEnd :: a) s (q ++ .frameEnd :: c))
  (cfg (if p = q then .found else .next) none
    (s.reverse ++ p ++ .frameEnd :: a) [] c) := by
 induction p generalizing q v s with
 | nil =>
   cases q with
   | nil =>
     have one : TM2.Reaches machine (cfg .scan v (.frameEnd :: a) s (.frameEnd :: c))
       (cfg .restoreFound (some .frameEnd) a (.frameEnd :: s) c) :=
       Relation.ReflTransGen.single (by rw [scan_end]; rfl)
     simpa [TM2.Reaches, List.reverse_cons, List.append_assoc] using
       one.trans (restore_all true (some .frameEnd) a (.frameEnd :: s) c)
   | cons y ys =>
     simpa [List.cons_append] using mismatch_drop .frameEnd y
       (Ne.symm (vq y (by simp))) (vq y (by simp)) ys
       (by intro z hz; exact vq z (by simp [hz])) v a s c
 | cons x xs ih =>
   cases q with
   | nil =>
     have one : TM2.Reaches machine
       (cfg .scan v (x :: (xs ++ .frameEnd :: a)) s (.frameEnd :: c))
       (cfg .restoreNext (some .tokenEnd) (xs ++ .frameEnd :: a) (x :: s) c) :=
       Relation.ReflTransGen.single (by rw [scan_mismatch x .frameEnd (vp x (by simp))]; rfl)
     simpa [TM2.Reaches, List.reverse_cons, List.cons_append, List.append_assoc] using
       one.trans (restore_all false (some .tokenEnd) (xs ++ .frameEnd :: a) (x :: s) c)
   | cons y ys =>
     by_cases hxy : x = y
     · subst y
       have one : TM2.Reaches machine
         (cfg .scan v (x :: (xs ++ .frameEnd :: a)) s (x :: (ys ++ .frameEnd :: c)))
         (cfg .scan (some .bit1) (xs ++ .frameEnd :: a) (x :: s) (ys ++ .frameEnd :: c)) :=
         Relation.ReflTransGen.single (by rw [scan_same x (vp x (by simp))]; rfl)
       have h := one.trans (ih ys (by intro z hz; exact vp z (by simp [hz]))
         (by intro z hz; exact vq z (by simp [hz])) (some .bit1) (x :: s))
       simpa [TM2.Reaches, List.reverse_cons, List.cons_append, List.append_assoc] using h
     · have h := mismatch_drop x y hxy (vq y (by simp)) ys
         (by intro z hz; exact vq z (by simp [hz])) v (xs ++ .frameEnd :: a) s c
       simpa [List.cons_append, List.append_assoc, hxy] using h



def frames (ps : List (List Symbol)) : List Symbol :=
 ps.flatMap (fun p => p ++ [.frameEnd])

theorem next_nonempty (x : Symbol) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step machine (cfg .next v a s (x :: c)) =
 some (cfg .scan (some x) a s (x :: c)) := by
 cases x <;> simp [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update]
 all_goals funext k; cases k <;> rfl

theorem next_empty (v : Option Symbol) (a s : List Symbol) :
 TM2.step machine (cfg .next v a s []) = some (cfg .absent none a s []) := by
 simp [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update]

theorem next_frame (p : List Symbol) (v : Option Symbol) (a c : List Symbol) :
 ∃ w, TM2.Reaches machine (cfg .next v a [] (p ++ .frameEnd :: c))
   (cfg .scan w a [] (p ++ .frameEnd :: c)) := by
 cases p with
 | nil => exact ⟨some .frameEnd, Relation.ReflTransGen.single (by rw [List.nil_append, next_nonempty]; rfl)⟩
 | cons x xs => exact ⟨some x, Relation.ReflTransGen.single (by rw [List.cons_append, next_nonempty]; rfl)⟩

/-- Total lookup on valid framed entries. Target is preserved; the context
prefix through the match is consumed, or all entries on failure. -/
theorem lookup_frames (p : List Symbol) (ps : List (List Symbol))
    (vp : ∀ x ∈ p, x ≠ .frameEnd)
    (vps : ∀ q ∈ ps, ∀ x ∈ q, x ≠ .frameEnd)
    (v : Option Symbol) (a : List Symbol) :
 ∃ rest, TM2.Reaches machine
   (cfg .next v (p ++ .frameEnd :: a) [] (frames ps))
   (cfg (if p ∈ ps then .found else .absent) none (p ++ .frameEnd :: a) [] rest) := by
 induction ps generalizing v with
 | nil =>
   refine ⟨[], Relation.ReflTransGen.single ?_⟩
   simp only [frames, List.flatMap_nil, List.not_mem_nil, ↓reduceIte]
   rw [next_empty]
   rfl
 | cons q qs ih =>
   obtain ⟨w, hn⟩ := next_frame q v (p ++ .frameEnd :: a) (frames qs)
   have hc := scan_frames p q vp (vps q (by simp)) w a [] (frames qs)
   have h := hn.trans hc
   by_cases he : p = q
   · refine ⟨frames qs, ?_⟩
     simpa [TM2.Reaches, frames, List.flatMap_cons, List.append_assoc, he] using h
   · obtain ⟨rest, hr⟩ := ih (by intro q hq; exact vps q (by simp [hq])) none
     have h' : TM2.Reaches machine
       (cfg .next v (p ++ .frameEnd :: a) [] (frames (q :: qs)))
       (cfg .next none (p ++ .frameEnd :: a) [] (frames qs)) := by
       simpa [TM2.Reaches, frames, List.flatMap_cons, List.append_assoc, he] using h
     exact ⟨rest, by simpa [TM2.Reaches, he] using h'.trans hr⟩

def formulaPayload (p : ZFR.Formula) : List Symbol :=
 payloadBits (ZFR.TokenVM.emitFormula p)
def contextFrames (Γ : ZFR.Context) : List Symbol := frames (Γ.map formulaPayload)

theorem formulaPayload_injective : Function.Injective formulaPayload :=
 payloadBits_injective.comp emitFormula_injective

/-- Concrete finite TM2 computes EXACT source-calculus context membership.
Context entries here are individually framed formulas, not a packed context
value. A packed-context decoder is still required by that alternative frontend. -/
theorem lookup_context (p : ZFR.Formula) (Γ : ZFR.Context)
    (v : Option Symbol) (a : List Symbol) :
 ∃ rest, TM2.Reaches machine
   (cfg .next v (formulaPayload p ++ .frameEnd :: a) [] (contextFrames Γ))
   (cfg (if p ∈ Γ then .found else .absent) none
     (formulaPayload p ++ .frameEnd :: a) [] rest) := by
 have h := lookup_frames (formulaPayload p) (Γ.map formulaPayload)
   (payloadBits_no_end _) (by intro q hq; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq; exact payloadBits_no_end _)
   v a
 have he : formulaPayload p ∈ Γ.map formulaPayload ↔ p ∈ Γ := by
   constructor
   · intro h; obtain ⟨q,hq,he⟩ := List.mem_map.mp h
     exact formulaPayload_injective he ▸ hq
   · exact fun hp => List.mem_map.mpr ⟨p,hp,rfl⟩
 simpa only [contextFrames, he] using h

end RosserDirect.Membership
