module
public import DirectTypedFrames
@[expose] public section
namespace RosserDirect.Append
open Turing
set_option backward.isDefEq.respectTransparency false

/-- Finite literal-word emission. Suffix is compiler-time syntax, never an
arbitrary runtime function on a stack. -/
def pushWord : List Symbol → Statement → Statement
 | [], q => q
 | x :: xs, q => .push .scratch (fun _ => x) (pushWord xs q)

theorem pushWord_correct (w : List Symbol) (q : Statement) (v : Option Symbol)
    (a b c : List Symbol) :
 TM2.stepAux (pushWord w q) v (storage a b c) =
 TM2.stepAux q v (storage a (w.reverse ++ b) c) := by
 induction w generalizing b with
 | nil => rfl
 | cons x xs ih =>
   simp only [pushWord, TM2.stepAux]
   have hu : Function.update (storage a b c) Stack.scratch (x :: b) =
     storage a (x :: b) c := by funext k; cases k <;> rfl
   change TM2.stepAux (pushWord xs q) v (Function.update (storage a b c) Stack.scratch (x :: b)) = _
   rw [hu, ih]
   simp [List.reverse_cons, List.append_assoc]

def machine (suffix : List Symbol) : Label → Statement
 | .scan => .pop .input (fun _ a => a)
   (.branch Option.isNone (.goto (fun _ => .reject))
    (.branch (fun a => a == some .frameEnd)
      (pushWord suffix (.push .scratch (fun _ => .frameEnd) (.goto (fun _ => .flush))))
      (.push .scratch (fun a => a.getD .bit0) (.goto (fun _ => .scan)))))
 | .flush => RosserDirect.machine .flush
 | .done => .halt
 | .reject => .halt

theorem scan_step (suffix : List Symbol) (x : Symbol) (hx : x ≠ .frameEnd)
    (v : Option Symbol) (a b c : List Symbol) :
 TM2.step (machine suffix) (cfg .scan v (x :: a) b c) =
 some (cfg .scan (some x) a (x :: b) c) := by
 cases x <;> simp_all [machine, cfg, storage, TM2.step, TM2.stepAux]
 all_goals funext k; cases k <;> rfl

theorem delimiter_step (suffix : List Symbol) (v : Option Symbol) (a b c : List Symbol) :
 TM2.step (machine suffix) (cfg .scan v (.frameEnd :: a) b c) =
 some (cfg .flush (some .frameEnd) a (.frameEnd :: (suffix.reverse ++ b)) c) := by
 simp only [TM2.step, cfg, machine, TM2.stepAux]
 have hu : Function.update (storage (.frameEnd :: a) b c) Stack.input a =
   storage a b c := by funext k; cases k <;> rfl
 change some (TM2.stepAux (pushWord suffix
   (.push .scratch (fun _ => .frameEnd) (.goto (fun _ => .flush))))
   (some .frameEnd) (Function.update (storage (.frameEnd :: a) b c) Stack.input a)) = _
 rw [hu, pushWord_correct]
 simp [cfg, TM2.stepAux]
 funext k; cases k <;> rfl

theorem flush_step (suffix : List Symbol) (x : Symbol) (v : Option Symbol)
    (a b c : List Symbol) :
 TM2.step (machine suffix) (cfg .flush v a (x :: b) c) =
 some (cfg .flush (some x) a b (x :: c)) := RosserDirect.flush_step x v a b c

theorem flush_empty (suffix : List Symbol) (v : Option Symbol) (a c : List Symbol) :
 TM2.step (machine suffix) (cfg .flush v a [] c) = some (cfg .done none a [] c) :=
 RosserDirect.flush_empty v a c

theorem scan_frame (suffix payload : List Symbol)
    (valid : ∀ x ∈ payload, x ≠ .frameEnd)
    (v : Option Symbol) (rest scratch out : List Symbol) :
 TM2.Reaches (machine suffix) (cfg .scan v (payload ++ .frameEnd :: rest) scratch out)
   (cfg .flush (some .frameEnd) rest
    (.frameEnd :: (suffix.reverse ++ payload.reverse ++ scratch)) out) := by
 induction payload generalizing v scratch with
 | nil =>
   apply Relation.ReflTransGen.single
   simp only [List.nil_append, List.reverse_nil, List.append_nil]
   rw [delimiter_step]
   rfl
 | cons x xs ih =>
   have hx := valid x (by simp)
   have hr := ih (by intro y hy; exact valid y (by simp [hy])) (some x) (x :: scratch)
   have one : TM2.Reaches (machine suffix)
     (cfg .scan v ((x :: xs) ++ .frameEnd :: rest) scratch out)
     (cfg .scan (some x) (xs ++ .frameEnd :: rest) (x :: scratch) out) :=
     Relation.ReflTransGen.single (by rw [List.cons_append, scan_step suffix x hx]; rfl)
   exact one.trans (by simpa [TM2.Reaches, List.reverse_cons, List.append_assoc] using hr)

theorem flush_frame (suffix : List Symbol) (v : Option Symbol) (rest scratch out : List Symbol) :
 TM2.Reaches (machine suffix) (cfg .flush v rest scratch out)
   (cfg .done none rest [] (scratch.reverse ++ out)) := by
 induction scratch generalizing v out with
 | nil =>
   apply Relation.ReflTransGen.single
   rw [flush_empty]
   rfl
 | cons x xs ih =>
   have one : TM2.Reaches (machine suffix) (cfg .flush v rest (x :: xs) out)
     (cfg .flush (some x) rest xs (x :: out)) :=
     Relation.ReflTransGen.single (by rw [flush_step]; rfl)
   exact one.trans (by simpa [TM2.Reaches, List.reverse_cons, List.append_assoc] using ih (some x) (x :: out))

/-- Appends literal constructor data while moving one frame. Linear scans,
finite alphabet/store/control, with exact preservation of unrelated frames. -/
theorem append_frame (suffix payload : List Symbol)
    (valid : ∀ x ∈ payload, x ≠ .frameEnd)
    (v : Option Symbol) (rest out : List Symbol) :
 TM2.Reaches (machine suffix) (cfg .scan v (payload ++ .frameEnd :: rest) [] out)
   (cfg .done none rest [] (payload ++ suffix ++ .frameEnd :: out)) := by
 have h := (scan_frame suffix payload valid v rest [] out).trans
   (flush_frame suffix (some .frameEnd) rest
    (.frameEnd :: (suffix.reverse ++ payload.reverse ++ [])) out)
 simpa [TM2.Reaches, List.reverse_cons, List.reverse_append, List.append_assoc] using h

theorem pushWord_support (w : List Symbol) (q : Statement)
    (h : TM2.SupportsStmt (Finset.univ : Finset Label) q) :
 TM2.SupportsStmt Finset.univ (pushWord w q) := by
 induction w with
 | nil => exact h
 | cons x xs ih => exact ih

end RosserDirect.Append
