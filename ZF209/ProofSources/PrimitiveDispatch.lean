module
public import PrimitiveFetch
@[expose] public section
namespace C209Search.Primitive.Dispatch
open M209.Source
private theorem row48 : program 48 = some (.dec 4 4329 49) := by decide +kernel
private theorem row49 : program 49 = some (.dec 4 4222 50) := by decide +kernel
private theorem decrement (r : Registers) :
 (fun j : Fin 9 => if j.val=4 then r j-1 else r j) = write r 4 (r 4-1) := by
 funext j
 have he : j.val=4 ↔ j=4 := by
  constructor
  · intro h; apply Fin.ext; exact h
  · intro h; subst j; rfl
 by_cases h : j=4 <;> simp_all [write]
private theorem step48 (r : Registers) :
 step ⟨48,r⟩ = if r 4=0 then ⟨4329,r⟩ else ⟨49,write r 4 (r 4-1)⟩ := by
 unfold step scalarNext
 rw [row48]
 simp only [Option.bind_some,scalarExecute]
 change (if r 4=0 then some (⟨4329,r⟩ : Configuration) else some (⟨49,_⟩ : Configuration)).getD _ = _
 rw [decrement]
 split <;> rfl
private theorem step49 (r : Registers) :
 step ⟨49,r⟩ = if r 4=0 then ⟨4222,r⟩ else ⟨50,write r 4 (r 4-1)⟩ := by
 unfold step scalarNext
 rw [row49]
 simp only [Option.bind_some,scalarExecute]
 change (if r 4=0 then some (⟨4222,r⟩ : Configuration) else some (⟨50,_⟩ : Configuration)).getD _ = _
 rw [decrement]
 split <;> rfl
private theorem write_same (r : Registers) (k : Fin 9) : write r k (r k) = r := by
  funext j
  simp only [write]
  split <;> simp_all

private theorem write_twice (r : Registers) (k : Fin 9) (a b : Nat) :
    write (write r k a) k b = write r k b := by
  funext j
  by_cases h : j = k <;> simp [write,h]

theorem zero (r : Registers) (ha : r 4 = 0) :
    Steps 1 ⟨48,r⟩ ⟨4329,r⟩ := by
  apply Steps.cons
  rw [step48]
  simp only [ha, ↓reduceIte]
  exact Steps.refl _

theorem one (r : Registers) (ha : r 4 = 1) :
    Steps 2 ⟨48,r⟩ ⟨4222,write r 4 0⟩ := by
  apply Steps.cons
  rw [step48]
  simp only [ha, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub]
  apply Steps.cons
  rw [step49]
  simp only [write, ↓reduceIte]
  exact Steps.refl _

theorem many (a : Nat) (r : Registers) (ha : r 4 = a+2) :
    Steps 2 ⟨48,r⟩ ⟨50,write r 4 a⟩ := by
  apply Steps.cons
  rw [step48]
  have hn : a+2 ≠ 0 := by omega
  simp only [ha, hn, ↓reduceIte]
  apply Steps.cons
  rw [step49]
  have hread : write r 4 (a+2-1) 4 = a+1 := by simp [write]
  have hn' : a+1 ≠ 0 := by omega
  simp only [hread, hn', ↓reduceIte, Nat.add_sub_cancel, write_twice]
  exact Steps.refl _

def target (a : Nat) : Nat := if a = 0 then 4329 else if a = 1 then 4222 else 50
def cost (a : Nat) : Nat := if a = 0 then 1 else 2

/-- Exact three-way dispatch: S, MP, or AX with selector minus two. -/
theorem total (a : Nat) (r : Registers) (ha : r 4 = a) :
    Steps (cost a) ⟨48,r⟩ ⟨(target a),write r 4 (a-2)⟩ := by
  cases a with
  | zero =>
    have hw : write r 4 0 = r := by rw [← ha]; exact write_same r 4
    simpa only [cost,target,↓reduceIte,Nat.zero_sub,hw] using zero r ha
  | succ a =>
    cases a with
    | zero => exact one r ha
    | succ a =>
      have ht : target (a+2) = 50 := by simp [target]
      have hc : cost (a+2) = 2 := by simp [cost]
      change Steps (cost (a+2)) ⟨48,r⟩ ⟨(target (a+2)),write r 4 (a+2-2)⟩
      simpa only [ht,hc,Nat.add_sub_cancel] using many a r ha


end C209Search.Primitive.Dispatch
