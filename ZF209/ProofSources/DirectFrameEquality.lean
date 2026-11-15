module
public import DirectTM2Frames
@[expose] public section
namespace RosserDirectEquality
set_option backward.isDefEq.respectTransparency false
open Turing RosserDirect
inductive Label where
 | scan | equal | different
 deriving DecidableEq, Fintype, Repr, Inhabited
abbrev Register := Option Symbol
abbrev Config := TM2.Cfg (fun _ : Stack => Symbol) Label Register

def cfg (q : Label) (v : Register) (a scratch b : List Symbol) : Config :=
 ⟨some q, v, storage a scratch b⟩

/-- Destructive, linear structural comparison of two delimiter-framed values.
All local data are finite; scratch and trailing frames are untouched. -/
def machine : Label → TM2.Stmt (fun _ : Stack => Symbol) Label Register
 | .scan => .pop .input (fun _ x => x)
   (.pop .output (fun v y => if v == y then v else none)
     (.branch Option.isSome
       (.branch (fun v => v == some .frameEnd)
         (.goto (fun _ => .equal)) (.goto (fun _ => .scan)))
       (.goto (fun _ => .different))))
 | .equal => .halt
 | .different => .halt

theorem same_step (x : Symbol) (hx : x ≠ .frameEnd) (v : Register)
    (a s b : List Symbol) :
 TM2.step machine (cfg .scan v (x :: a) s (x :: b)) =
 some (cfg .scan (some x) a s b) := by
 cases x <;> simp_all [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update] <;>
 funext k <;> cases k <;> rfl

theorem delimiter_step (v : Register) (a s b : List Symbol) :
 TM2.step machine (cfg .scan v (.frameEnd :: a) s (.frameEnd :: b)) =
 some (cfg .equal (some .frameEnd) a s b) := by
 simp [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update] <;>
 funext k <;> cases k <;> rfl

theorem different_step (x y : Symbol) (h : x ≠ y) (v : Register)
    (a s b : List Symbol) :
 TM2.step machine (cfg .scan v (x :: a) s (y :: b)) =
 some (cfg .different none a s b) := by
 cases x <;> cases y <;>
 simp_all [machine, cfg, storage, TM2.step, TM2.stepAux, Function.update] <;>
 funext k <;> cases k <;> rfl

theorem equal_frames (p : List Symbol) (valid : ∀ x ∈ p, x ≠ .frameEnd)
    (v : Register) (a s b : List Symbol) :
 TM2.Reaches machine (cfg .scan v (p ++ .frameEnd :: a) s (p ++ .frameEnd :: b))
   (cfg .equal (some .frameEnd) a s b) := by
 induction p generalizing v with
 | nil => exact Relation.ReflTransGen.single (by simp only [List.nil_append]; rw [delimiter_step]; rfl)
 | cons x xs ih =>
   have hx := valid x (by simp)
   have one : TM2.Reaches machine
     (cfg .scan v ((x :: xs) ++ .frameEnd :: a) s ((x :: xs) ++ .frameEnd :: b))
     (cfg .scan (some x) (xs ++ .frameEnd :: a) s (xs ++ .frameEnd :: b)) :=
     Relation.ReflTransGen.single (by rw [List.cons_append, List.cons_append, same_step x hx]; rfl)
   exact one.trans (ih (by intro y hy; exact valid y (by simp [hy])) _)

theorem unequal_frames (p q : List Symbol)
    (vp : ∀ x ∈ p, x ≠ .frameEnd) (vq : ∀ x ∈ q, x ≠ .frameEnd) (hne : p ≠ q)
    (v : Register) (a s b : List Symbol) :
 ∃ w left right, TM2.Reaches machine
   (cfg .scan v (p ++ .frameEnd :: a) s (q ++ .frameEnd :: b))
   (cfg .different w left s right) := by
 induction p generalizing q v with
 | nil =>
   cases q with
   | nil => exact False.elim (hne rfl)
   | cons y ys =>
     refine ⟨none, a, ys ++ .frameEnd :: b, Relation.ReflTransGen.single ?_⟩
     rw [List.nil_append, List.cons_append, different_step .frameEnd y (Ne.symm (vq y (by simp)))]
     rfl
 | cons x xs ih =>
   cases q with
   | nil =>
     refine ⟨none, xs ++ .frameEnd :: a, b, Relation.ReflTransGen.single ?_⟩
     rw [List.nil_append, List.cons_append, different_step x .frameEnd (vp x (by simp))]
     rfl
   | cons y ys =>
     by_cases hxy : x = y
     · subst y
       have hne' : xs ≠ ys := by intro h; exact hne (congrArg (List.cons x) h)
       obtain ⟨w,l,r,h⟩ := ih ys (by intro z hz; exact vp z (by simp [hz]))
         (by intro z hz; exact vq z (by simp [hz])) hne' (some x)
       refine ⟨w,l,r, ?_⟩
       have one : TM2.Reaches machine
         (cfg .scan v ((x :: xs) ++ .frameEnd :: a) s ((x :: ys) ++ .frameEnd :: b))
         (cfg .scan (some x) (xs ++ .frameEnd :: a) s (ys ++ .frameEnd :: b)) :=
         Relation.ReflTransGen.single (by rw [List.cons_append, List.cons_append, same_step x (vp x (by simp))]; rfl)
       exact one.trans h
     · refine ⟨none, xs ++ .frameEnd :: a, ys ++ .frameEnd :: b, Relation.ReflTransGen.single ?_⟩
       rw [List.cons_append, List.cons_append, different_step x y hxy]
       rfl

end RosserDirectEquality
