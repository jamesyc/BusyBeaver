module
public import I3_334Support.Search.Compiler.Forward
@[expose] public section

namespace PalomarI3380.Compiler

def storeOf {V : Type} [OfNat V 0] (allRegisters : List V) : Store V :=
  fun r => allRegisters[allRegisters.length - (r.val + 1)]?.getD 0

theorem storeOf_set {V : Type} [OfNat V 0] (rs : List V) (hLen : 12 ≤ rs.length) (p : Register) (value : V) :
    storeOf (rs.set (rs.length - (p.val + 1)) value) = (storeOf rs).set p value := by
  funext r
  unfold storeOf Store.set
  simp only [List.length_set]
  by_cases eq : r = p
  · subst r
    have idx : rs.length - (p.val + 1) < rs.length := by have h := p.isLt; omega
    simp only [List.getElem?_set_self idx, Option.getD_some, ↓reduceIte]
  · have different : rs.length - (r.val + 1) ≠ rs.length - (p.val + 1) := by
      intro same
      apply eq
      apply Fin.ext
      have hr := r.isLt
      have hp := p.isLt
      omega
    simp only [eq, ↓reduceIte, List.getElem?_set_ne different.symm]

end PalomarI3380.Compiler
