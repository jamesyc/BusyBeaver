module
public import DirectTypedFrames
@[expose] public section
namespace RosserDirect.Copy
open Turing
set_option backward.isDefEq.respectTransparency false

/-- Non-destructive copying of one framed value, with finite labels/registers.
The scan temporarily reverses the input frame; flush restores input and emits
a second copy to output. No unbounded host-language callback is used. -/
def machine : Label → Statement
 | .scan => .pop .input (fun _ a => a)
   (.branch Option.isNone (.goto (fun _ => .reject))
    (.push .scratch (fun a => a.getD .bit0)
     (.branch (fun a => a == some .frameEnd)
      (.goto (fun _ => .flush)) (.goto (fun _ => .scan)))))
 | .flush => .pop .scratch (fun _ a => a)
   (.branch Option.isNone (.goto (fun _ => .done))
    (.push .input (fun a => a.getD .bit0)
     (.push .output (fun a => a.getD .bit0) (.goto (fun _ => .flush)))))
 | .done => .halt
 | .reject => .halt

theorem scan_step (x : Symbol) (hx : x ≠ .frameEnd) (v : Option Symbol)
    (a b c : List Symbol) :
 TM2.step machine (cfg .scan v (x :: a) b c) =
 some (cfg .scan (some x) a (x :: b) c) := by
 cases x <;> simp_all [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update] <;> funext k <;> cases k <;> rfl

theorem delimiter_step (v : Option Symbol) (a b c : List Symbol) :
 TM2.step machine (cfg .scan v (.frameEnd :: a) b c) =
 some (cfg .flush (some .frameEnd) a (.frameEnd :: b) c) := by
 simp [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update] <;> funext k <;> cases k <;> rfl

theorem flush_step (x : Symbol) (v : Option Symbol) (a b c : List Symbol) :
 TM2.step machine (cfg .flush v a (x :: b) c) =
 some (cfg .flush (some x) (x :: a) b (x :: c)) := by
 cases x <;> simp [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update] <;> funext k <;> cases k <;> rfl

theorem flush_empty (v : Option Symbol) (a c : List Symbol) :
 TM2.step machine (cfg .flush v a [] c) = some (cfg .done none a [] c) := by
 simp [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update] <;> funext k <;> cases k <;> rfl

theorem scan_frame (payload : List Symbol)
    (valid : ∀ x ∈ payload, x ≠ .frameEnd)
    (v : Option Symbol) (rest scratch out : List Symbol) :
 TM2.Reaches machine (cfg .scan v (payload ++ .frameEnd :: rest) scratch out)
   (cfg .flush (some .frameEnd) rest (.frameEnd :: (payload.reverse ++ scratch)) out) := by
 induction payload generalizing v scratch with
 | nil =>
   apply Relation.ReflTransGen.single
   simp only [List.nil_append, List.reverse_nil]
   rw [delimiter_step]
   rfl
 | cons x xs ih =>
   have hx := valid x (by simp)
   have hr := ih (by intro y hy; exact valid y (by simp [hy])) (some x) (x :: scratch)
   have one : TM2.Reaches machine
     (cfg .scan v ((x :: xs) ++ .frameEnd :: rest) scratch out)
     (cfg .scan (some x) (xs ++ .frameEnd :: rest) (x :: scratch) out) :=
     Relation.ReflTransGen.single (by rw [List.cons_append, scan_step x hx]; rfl)
   exact one.trans (by simpa [TM2.Reaches, List.reverse_cons, List.append_assoc] using hr)

theorem flush_frame (v : Option Symbol) (rest scratch out : List Symbol) :
 TM2.Reaches machine (cfg .flush v rest scratch out)
   (cfg .done none (scratch.reverse ++ rest) [] (scratch.reverse ++ out)) := by
 induction scratch generalizing v rest out with
 | nil =>
   apply Relation.ReflTransGen.single
   rw [flush_empty]
   rfl
 | cons x xs ih =>
   have one : TM2.Reaches machine (cfg .flush v rest (x :: xs) out)
     (cfg .flush (some x) (x :: rest) xs (x :: out)) :=
     Relation.ReflTransGen.single (by rw [flush_step]; rfl)
   exact one.trans (by simpa [TM2.Reaches, List.reverse_cons, List.append_assoc] using ih (some x) (x :: rest) (x :: out))

/-- Complete finite multistack routine: copies one delimiter-framed value,
preserves token order and both surrounding stacks, and restores empty scratch.
It uses one scan and one flush per symbol, rather than repeated indexed reads. -/
theorem copy_frame (payload : List Symbol)
    (valid : ∀ x ∈ payload, x ≠ .frameEnd)
    (v : Option Symbol) (rest out : List Symbol) :
 TM2.Reaches machine (cfg .scan v (payload ++ .frameEnd :: rest) [] out)
   (cfg .done none (payload ++ .frameEnd :: rest) [] (payload ++ .frameEnd :: out)) := by
 have h := (scan_frame payload valid v rest [] out).trans
   (flush_frame (some .frameEnd) rest (.frameEnd :: (payload.reverse ++ [])) out)
 simpa [TM2.Reaches, List.reverse_cons, List.append_assoc] using h

end RosserDirect.Copy
