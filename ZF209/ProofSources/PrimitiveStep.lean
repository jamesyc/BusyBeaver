module
public import M209.SourceData
public import M209.SourceScalarEndpoint
public import M6.Source.Cantor
@[expose] public section
namespace C209Search.Primitive
open M209.Source
abbrev Registers := Fin 9 → Nat
abbrev Configuration := ScalarState

def write (r : Registers) (i : Fin 9) (v : Nat) : Registers := fun k => if k=i then v else r k

def step (s : Configuration) : Configuration := (scalarNext program s).getD s

inductive Steps : Nat → Configuration → Configuration → Prop
 | refl (s) : Steps 0 s s
 | cons : Steps n (step s) t → Steps (n+1) s t

theorem steps_trans (ab : Steps n a b) (bc : Steps m b c) : Steps (n+m) a c := by
 induction ab with
 | refl => simpa using bc
 | cons h ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Steps.cons (ih bc)

def runSource : Nat → Configuration → Option Configuration
 | 0,s => some s
 | n+1,s => (scalarNext program s).bind (runSource n)

theorem steps_from_halt (n : Nat) (s t : Configuration)
 (hs : scalarNext program s = none) (h : Steps n s t) : t=s := by
 induction n generalizing s t with
 | zero => cases h; rfl
 | succ n ih =>
   cases h with
   | cons h =>
     have he : step s=s := by simp [step,hs]
     rw [he] at h
     exact ih s t hs h

theorem steps_real (n : Nat) (s t : Configuration)
 (h : Steps n s t) (ht : scalarNext program t ≠ none) : runSource n s = some t := by
 induction n generalizing s t with
 | zero => cases h; rfl
 | succ n ih =>
   cases h with
   | cons h =>
     cases hs : scalarNext program s with
     | none =>
       have he : step s=s := by simp [step,hs]
       rw [he] at h
       have heq := steps_from_halt n s t hs h
       exact False.elim (ht (heq.symm ▸ hs))
     | some mid =>
       have he : step s=mid := by simp [step,hs]
       rw [he] at h
       simpa [runSource,hs] using ih mid t h ht
end C209Search.Primitive
