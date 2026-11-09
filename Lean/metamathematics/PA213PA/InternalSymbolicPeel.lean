module

public import PA213PA.InternalSymbolicWords
public import PA213PA.InternalNativeRows

@[expose] public section
namespace PA213.PA.InternalTrace.Symbolic
open PA215
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ScanBits PA215.Runtime
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma affine_succ (a c : Nat) (n : V) : (a : V)*n+(c+1 : Nat) = ((a : V)*n+c)+1 := by
  simp only [Nat.cast_add,Nat.cast_one,add_assoc]

theorem peel_left {q : Nat} {b : Bool} {a c : Nat} {l r : List Seg} {s' : SConf} {m : Bool}
    (n : V) (box : BoxSt → V → V) (control : Nat → V)
    (h : Runtime.peelLeft q b a c l r=some (s',m)) :
    m=false ∧ config n box control (q,true,.run b a c::l,r)=config n box control s' := by
  unfold Runtime.peelLeft at h
  split at h
  · simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    refine ⟨rfl,?_⟩
    simp only [config,word,affine_succ,repeat_succ]
  · simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    refine ⟨rfl,?_⟩
    simp [config,word]
  · simp at h

theorem peel_right {q : Nat} {b : Bool} {a c : Nat} {l r : List Seg} {s' : SConf} {m : Bool}
    (n : V) (box : BoxSt → V → V) (control : Nat → V)
    (h : Runtime.peelRight q b a c l r=some (s',m)) :
    m=false ∧ config n box control (q,false,l,.run b a c::r)=config n box control s' := by
  unfold Runtime.peelRight at h
  split at h
  · simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    refine ⟨rfl,?_⟩
    simp only [config,word,affine_succ,repeat_succ]
  · simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    refine ⟨rfl,?_⟩
    simp [config,word]
  · simp at h
end Models
#print axioms peel_left
#print axioms peel_right
end PA213.PA.InternalTrace.Symbolic

