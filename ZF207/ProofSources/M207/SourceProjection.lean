module
public import M207.SourceDefinitions
@[expose] public section
namespace M207.Source
open M6.Runtime

/-- Nine scalar registers, in physical order. The fixed permutation below
exposes their original logical names. No gap or spare-register tail is stored. -/
structure ScalarState where
  pc : Nat
  registers : Fin 9 → Nat

def project (s : State) : ScalarState := ⟨s.pc,fun r => s.file.getD r.val 0⟩
def registerIndex (r : Nat) : Fin 9 := ⟨r%9,Nat.mod_lt _ (by decide)⟩
def scalarExecute : Instruction → ScalarState → Option ScalarState
  | .inc r k, s => some ⟨k,fun j => if j.val = r then s.registers j + 1 else s.registers j⟩
  | .dec r z p, s =>
    if s.registers (registerIndex r) = 0 then some ⟨z,s.registers⟩
    else some ⟨p,fun j => if j.val = r then s.registers j - 1 else s.registers j⟩
  | .jump k, s => some ⟨k,s.registers⟩
  | .halt, _ => none

def scalarNext (program : Nat → Option Instruction) (s : ScalarState) : Option ScalarState :=
  (program s.pc).bind fun code => scalarExecute code s

private theorem getD_incr (vs : List Nat) (i j : Nat) (hi : i < vs.length) :
    (incr i vs).getD j 0 = if j = i then vs.getD j 0 + 1 else vs.getD j 0 := by
  induction vs generalizing i j with
  | nil => simp at hi
  | cons v vs ih => cases i <;> cases j <;> simp_all [incr, List.getD]
private theorem getD_decr (vs : List Nat) (i j : Nat) (hi : i < vs.length) :
    (decr i vs).getD j 0 = if j = i then vs.getD j 0 - 1 else vs.getD j 0 := by
  induction vs generalizing i j with
  | nil => simp at hi
  | cons v vs ih => cases i <;> cases j <;> simp_all [decr, List.getD]
private theorem getD_append_left (vs ws : List Nat) (i : Nat) (hi : i < vs.length) :
    (vs ++ ws).getD i 0 = vs.getD i 0 := by
  induction vs generalizing i with
  | nil => simp at hi
  | cons v vs ih => cases i <;> simp_all [List.getD]

theorem execute_projection {count : Nat} {code : Instruction} {s : State}
    (bound : instructionBound count code) (valid : Valid count s) :
    scalarExecute code (project s) = (execute code s).map project := by
  obtain ⟨hp,hf⟩ := valid
  cases code with
  | inc r k =>
    have hi : r < s.file.length := by have := bound.1; omega
    simp only [scalarExecute,execute,project,Option.map_some]
    congr 2
    funext j
    rw [getD_append_left _ _ _ (by simpa using Nat.lt_of_lt_of_le j.isLt (by omega : 9 ≤ s.file.length)),getD_incr _ _ _ hi]
  | dec r z p =>
    have hi : r < s.file.length := by have := bound.1; omega
    have hm : r%9 = r := Nat.mod_eq_of_lt bound.1
    simp only [scalarExecute,execute,project,registerIndex,hm]
    split
    · simp_all [project]
    · simp_all only [ite_false,Option.map_some]
      congr 2
      funext j
      rw [getD_decr _ _ _ hi]
      split <;> simp_all
  | jump k => rfl
  | halt => rfl
end M207.Source
