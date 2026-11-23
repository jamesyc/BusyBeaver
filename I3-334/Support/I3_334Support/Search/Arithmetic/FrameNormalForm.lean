module
public import I3_334Support.Search.Compiler.RegisterFile
public import I3_334Support.Search.Arithmetic.StoreCode
public import I3_334Support.Engine.Tape
@[expose] public section

namespace PalomarI3380.Compiler

/-- The rightmost physical register represents logical register zero. -/
def Store.file {V : Type} (s : Store V) : List V := (List.ofFn s).reverse

@[simp] theorem Store.length_file {V : Type} (s : Store V) : s.file.length = 12 := by
  simp [Store.file,Register]

theorem file_storeOf {V : Type} [OfNat V 0] (file : List V) (length : 12 ≤ file.length) :
    (storeOf file).file = file.drop (file.length-12) := by
  apply List.ext_getElem
  · simp only [Store.length_file,List.length_drop]; omega
  · intro i h₁ h₂
    have small : i < 12 := by simpa only [Store.length_file] using h₁
    unfold Store.file at h₁ ⊢
    rw [List.getElem_reverse,List.getElem_ofFn,List.getElem_drop]
    simp only [storeOf,List.length_ofFn,Fin.val_mk]
    have index : file.length-(12-1-i+1) = file.length-12+i := by omega
    rw [index,List.getElem?_eq_getElem (by rw [List.length_drop] at h₂; omega),Option.getD_some]

theorem storeOf_file {V : Type} [OfNat V 0] (stem : List V) (s : Store V) :
    storeOf (stem ++ s.file) = s := by
  funext r
  have index : (stem ++ s.file).length-(r.val+1) = stem.length+(12-1-r.val) := by
    simp only [List.length_append,Store.length_file]
    have small := r.isLt
    omega
  rw [storeOf,index,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  rw [List.getElem?_eq_getElem (by rw [Store.length_file]; have small := r.isLt; omega)]
  simp only [Option.getD_some,Store.file,List.getElem_reverse,List.getElem_ofFn,List.length_ofFn]
  congr 1
  apply Fin.ext
  change 12-1-(12-1-r.val) = r.val
  have small := r.isLt
  omega

theorem trimPC_zeros (path : List Bool) (n : Nat) : trimPC (path ++ Engine.zeros n) = trimPC path := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show Engine.zeros (n+1) = Engine.zeros n ++ [false] from List.replicate_succ' ..,
      ← List.append_assoc,trimPC_append_zero,ih]

end PalomarI3380.Compiler
