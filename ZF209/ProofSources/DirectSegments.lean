module
public import DirectFrameAppend
@[expose] public section
namespace RosserDirect.Segment
open Turing
set_option backward.isDefEq.respectTransparency false

abbrev Stmt (L : Type) := TM2.Stmt (fun _ : Stack => Symbol) L (Option Symbol)
abbrev Config (L : Type) := TM2.Cfg (fun _ : Stack => Symbol) L (Option Symbol)
def config {L : Type} (q : L) (reg : Option Symbol) (a b c : List Symbol) : Config L :=
 ⟨some q, reg, storage a b c⟩

def pushWord {L : Type} : List Symbol → Stmt L → Stmt L
 | [], q => q
 | x :: xs, q => .push .scratch (fun _ => x) (pushWord xs q)

theorem pushWord_correct {L : Type} (w : List Symbol) (q : Stmt L) (v : Option Symbol)
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

def scanStmt {L : Type} (again flush fail : L) (suffix : List Symbol) : Stmt L :=
 .pop .input (fun _ a => a)
   (.branch Option.isNone (.goto (fun _ => fail))
    (.branch (fun a => a == some .frameEnd)
      (pushWord suffix (.goto (fun _ => flush)))
      (.push .scratch (fun a => a.getD .bit0) (.goto (fun _ => again)))))

def flushStmt {L : Type} (again next : L) : Stmt L :=
 .pop .scratch (fun _ a => a)
   (.branch Option.isNone (.goto (fun _ => next))
    (.push .output (fun a => a.getD .bit0) (.goto (fun _ => again))))

variable {L : Type} (M : L → Stmt L) (scan flush next fail : L) (suffix : List Symbol)
variable (hs : M scan = scanStmt scan flush fail suffix)
variable (hf : M flush = flushStmt flush next)

include hs in
theorem scan_step (x : Symbol) (hx : x ≠ .frameEnd) (v : Option Symbol)
    (a b c : List Symbol) :
 TM2.step M (config scan v (x :: a) b c) =
 some (config scan (some x) a (x :: b) c) := by
 cases x <;> simp_all [config, storage, TM2.step, hs, scanStmt, TM2.stepAux]
 all_goals funext k; cases k <;> rfl

include hs in
theorem delimiter_step (v : Option Symbol) (a b c : List Symbol) :
 TM2.step M (config scan v (.frameEnd :: a) b c) =
 some (config flush (some .frameEnd) a (suffix.reverse ++ b) c) := by
 simp only [TM2.step, config, hs, scanStmt, TM2.stepAux]
 have hu : Function.update (storage (.frameEnd :: a) b c) Stack.input a =
   storage a b c := by funext k; cases k <;> rfl
 change some (TM2.stepAux (pushWord suffix (.goto (fun _ => flush)))
   (some .frameEnd) (Function.update (storage (.frameEnd :: a) b c) Stack.input a)) = _
 rw [hu, pushWord_correct]
 rfl

include hf in
theorem flush_step (x : Symbol) (v : Option Symbol) (a b c : List Symbol) :
 TM2.step M (config flush v a (x :: b) c) =
 some (config flush (some x) a b (x :: c)) := by
 cases x <;> simp [config, TM2.step, hf, flushStmt, TM2.stepAux, storage]
 all_goals funext k; cases k <;> rfl

include hf in
theorem flush_empty (v : Option Symbol) (a c : List Symbol) :
 TM2.step M (config flush v a [] c) = some (config next none a [] c) := by
 simp [config, TM2.step, hf, flushStmt, TM2.stepAux, storage, Function.update]

include hs in
theorem scan_frame (payload : List Symbol)
    (valid : ∀ x ∈ payload, x ≠ .frameEnd)
    (v : Option Symbol) (rest scratch out : List Symbol) :
 TM2.Reaches M (config scan v (payload ++ .frameEnd :: rest) scratch out)
   (config flush (some .frameEnd) rest (suffix.reverse ++ payload.reverse ++ scratch) out) := by
 induction payload generalizing v scratch with
 | nil =>
   apply Relation.ReflTransGen.single
   simp only [List.nil_append, List.reverse_nil, List.append_nil]
   rw [delimiter_step M scan flush fail suffix hs]
   rfl
 | cons x xs ih =>
   have hx := valid x (by simp)
   have hr := ih (by intro y hy; exact valid y (by simp [hy])) (some x) (x :: scratch)
   have one : TM2.Reaches M
     (config scan v ((x :: xs) ++ .frameEnd :: rest) scratch out)
     (config scan (some x) (xs ++ .frameEnd :: rest) (x :: scratch) out) :=
     Relation.ReflTransGen.single (by rw [List.cons_append, scan_step M scan flush fail suffix hs x hx]; rfl)
   exact one.trans (by simpa [TM2.Reaches, List.reverse_cons, List.append_assoc] using hr)

include hf in
theorem flush_frame (v : Option Symbol) (rest scratch out : List Symbol) :
 TM2.Reaches M (config flush v rest scratch out)
   (config next none rest [] (scratch.reverse ++ out)) := by
 induction scratch generalizing v out with
 | nil =>
   apply Relation.ReflTransGen.single
   rw [flush_empty M flush next hf]
   rfl
 | cons x xs ih =>
   have one : TM2.Reaches M (config flush v rest (x :: xs) out)
     (config flush (some x) rest xs (x :: out)) :=
     Relation.ReflTransGen.single (by rw [flush_step M flush next hf]; rfl)
   exact one.trans (by simpa [TM2.Reaches, List.reverse_cons, List.append_assoc] using ih (some x) (x :: out))

include hs hf in
/-- Embeddable subroutine theorem: the ambient machine's only requirements are
its two concrete routine bodies. `next` may be another phase, not a halting label. -/
theorem transfer (payload : List Symbol)
    (valid : ∀ x ∈ payload, x ≠ .frameEnd)
    (v : Option Symbol) (rest out : List Symbol) :
 TM2.Reaches M (config scan v (payload ++ .frameEnd :: rest) [] out)
   (config next none rest [] (payload ++ suffix ++ out)) := by
 have h := (scan_frame M scan flush fail suffix hs payload valid v rest [] out).trans
   (flush_frame M flush next hf (some .frameEnd) rest
    (suffix.reverse ++ payload.reverse ++ []) out)
 simpa [TM2.Reaches, List.reverse_append, List.append_assoc] using h

theorem pushWord_support [Fintype L] (w : List Symbol) (q : Stmt L)
    (h : TM2.SupportsStmt (Finset.univ : Finset L) q) :
 TM2.SupportsStmt Finset.univ (pushWord w q) := by
 induction w with
 | nil => exact h
 | cons x xs ih => exact ih

@[simp] theorem scanStmt_support [Fintype L] (a b c : L) (w : List Symbol) :
 TM2.SupportsStmt Finset.univ (scanStmt a b c w) := by
 simp only [scanStmt, TM2.SupportsStmt]
 constructor
 · simp
 · constructor
   · apply pushWord_support; simp [TM2.SupportsStmt]
   · simp

@[simp] theorem flushStmt_support [Fintype L] (a b : L) :
 TM2.SupportsStmt Finset.univ (flushStmt a b) := by simp [flushStmt, TM2.SupportsStmt]

end RosserDirect.Segment
