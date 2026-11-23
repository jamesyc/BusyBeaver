module
public import I3_334Support.Engine.ControlWords
@[expose] public section

namespace PalomarI3380.Engine

theorem split_register {α : Type} [OfNat α 0] (rs : List α) (r : Fin 12) (hLen : 13 ≤ rs.length) :
    ∃ a as v after,
      rs = (a :: as) ++ v :: after ∧ after.length = r.val ∧
      rs[rs.length - (r.val + 1)]?.getD 0 = v ∧
      ∀ value, rs.set (rs.length - (r.val + 1)) value = (a :: as) ++ value :: after := by
  let i := rs.length - (r.val + 1)
  have hIndex : i < rs.length := by dsimp only [i]; omega
  have positive : 0 < i := by have hr := r.isLt; dsimp only [i]; omega
  have hBefore : (rs.take i).length = i := List.length_take_of_le (by omega)
  obtain ⟨a, as, hTake⟩ := List.exists_cons_of_ne_nil (l := rs.take i)
    (by intro h; rw [h, List.length_nil] at hBefore; omega)
  refine ⟨a, as, rs[i], rs.drop (i + 1), ?_, ?_, ?_, ?_⟩
  · rw [← hTake]
    change rs = rs.take i ++ ([rs[i]] ++ rs.drop (i + 1))
    rw [← List.append_assoc, ← List.take_succ_eq_append_getElem hIndex, List.take_append_drop]
  · simp only [List.length_drop, i]
    omega
  · change rs[i]?.getD 0 = rs[i]
    rw [List.getElem?_eq_getElem hIndex]
    rfl
  · intro value
    change rs.set i value = _
    rw [← hTake, List.set_eq_take_append_cons_drop, ite_eq_left hIndex]

end PalomarI3380.Engine
