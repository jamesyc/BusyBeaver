module
public import I3_334.Machine.Bindings
@[expose] public section

namespace PalomarI3334

attribute [local irreducible] literal packedLiteral

def sourceRow (q : Fin 334) (read : Bool) : Nat :=
  literal[2*q.val+read.toNat]?.getD 0

def sourceWrites (q : Fin 334) (read : Bool) : Bool := sourceRow q read / 2 % 2 == 1

def sourceMovesRight (q : Fin 334) (read : Bool) : Bool := sourceRow q read % 2 == 1

def sourceTarget (q : Fin 334) (read : Bool) : Nat := sourceRow q read / 4

theorem sourceWrites_eq (q : Fin 334) (read : Bool) :
    sourceWrites q read = (Nat.mod (Nat.div (sourceRow q read) 2) 2 == 1) := rfl

theorem sourceTarget_eq (q : Fin 334) (read : Bool) :
    sourceTarget q read = Nat.div (sourceRow q read) 4 := rfl

theorem sourceRow_index (q : Fin 334) (read : Bool) :
    2*q.val+read.toNat < literal.size := by
  have hq := q.isLt
  have hb : read.toNat < 2 := by cases read <;> decide
  rw [literal_binding.2.1]
  omega

theorem sourceRow_lookup (q : Fin 334) (read : Bool) :
    machine.row q.val read.toNat = sourceRow q read := by
  let i := 2*q.val+read.toNat
  have iBound : i < literal.size := sourceRow_index q read
  have listBound : i < literal.toList.zipIdx.length :=
    (List.length_zipIdx.trans Array.length_toList).symm ▸ iBound
  have rowIn : (literal[i],i) ∈ literal.toList.zipIdx := by
    have hit := List.getElem_mem (l := literal.toList.zipIdx) (n := i) (h := listBound)
    simpa only [List.getElem_zipIdx,Array.getElem_toList,Nat.zero_add] using hit
  have source := List.all_eq_true.mp literal_binding.2.2.1 _ rowIn
  have hb : read.toNat < 2 := by cases read <;> decide
  have address : i / 2 = q.val := by dsimp [i]; omega
  have side : i % 2 = read.toNat := by dsimp [i]; omega
  simp only [beq_iff_eq,address,side] at source
  simpa only [sourceRow,← show i = 2*q.val+read.toNat from rfl,Array.getElem?_eq_getElem iBound,
    Option.getD_some] using source

theorem sourceRow_target (q : Fin 334) (read : Bool) : sourceRow q read / 4 ≤ 334 := by
  let i := 2*q.val+read.toNat
  have iBound : i < literal.size := sourceRow_index q read
  have li : i < literal.toList.length := Array.length_toList.symm ▸ iBound
  have member : literal[i] ∈ literal.toList := by
    simpa only [Array.getElem_toList] using List.getElem_mem (l := literal.toList) (n := i) (h := li)
  have h := List.all_eq_true.mp literal_binding.2.2.2.1 _ member
  simpa only [sourceRow,← show i = 2*q.val+read.toNat from rfl,Array.getElem?_eq_getElem iBound,
    Option.getD_some,decide_eq_true_eq] using h

end PalomarI3334
