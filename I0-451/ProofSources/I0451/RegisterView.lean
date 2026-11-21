module
public import I0451.ControlFlow

/-! The physical register tape has a fixed filler prefix and the nine
live registers in reverse register order. -/
@[expose] public section
namespace I0451.Runtime

def tapeRegistersWith {α : Type} (filler : List α) (regs : Fin 9 → α) : List α :=
  filler ++ (List.ofFn regs).reverse

def tapeRegisters (regs : Registers) : List Nat := tapeRegistersWith fixedBlocks regs

theorem tapeRegistersWith_reverse {α : Type} (filler : List α) (regs : Fin 9 → α) :
    (tapeRegistersWith filler regs).reverse = List.ofFn regs ++ filler.reverse := by
  simp [tapeRegistersWith, List.reverse_append]

theorem tapeRegisters_reverse (regs : Registers) :
    (tapeRegisters regs).reverse = List.ofFn regs ++ fixedBlocks.reverse := by
  exact tapeRegistersWith_reverse fixedBlocks regs

theorem tapeRegisters_length (regs : Registers) : (tapeRegisters regs).length = 201 := by
  have filler : fixedBlocks.length = 192 := by decide +kernel
  simp only [tapeRegisters, tapeRegistersWith, List.length_append, List.length_reverse, List.length_ofFn, filler]

private theorem cut_reversed {α : Type} {filler : List α} {regs : Fin 9 → α}
    {i : Fin 9} {cut : RegisterCut α}
    (found : cutRegister i.val (tapeRegistersWith filler regs) = some cut) :
    List.ofFn regs ++ filler.reverse =
      cut.after.reverse ++ cut.value :: cut.last :: cut.before.reverse := by
  have h := congrArg List.reverse (cutRegister_sound found).1
  simpa [tapeRegistersWith_reverse, List.reverse_append, List.reverse_cons, List.append_assoc] using h

theorem cutRegister_value_with {α : Type} {filler : List α} {regs : Fin 9 → α}
    {i : Fin 9} {cut : RegisterCut α}
    (found : cutRegister i.val (tapeRegistersWith filler regs) = some cut) :
    cut.value = regs i := by
  have reverse := cut_reversed found
  have index := (cutRegister_sound found).2
  have bound : i.val < (List.ofFn regs).length := by simp
  have left : (List.ofFn regs ++ filler.reverse)[i.val]? = some (regs i) := by
    rw [List.getElem?_append_left bound, List.getElem?_eq_getElem bound, List.getElem_ofFn]
  have right : (cut.after.reverse ++ cut.value :: cut.last :: cut.before.reverse)[i.val]? =
      some cut.value := by
    have skip : cut.after.reverse.length = i.val := by simpa using index
    rw [← skip, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  rw [reverse, right] at left
  exact Option.some.inj left

private theorem put_ofFn {α : Type} (regs : Fin 9 → α) (i : Fin 9) (new : α) :
    List.ofFn (putRegister regs i new) = (List.ofFn regs).set i.val new := by
  apply List.ext_getElem
  · simp
  · intro n first second
    have inside : n < 9 := by simpa using first
    rw [List.getElem_ofFn, List.getElem_set, List.getElem_ofFn]
    by_cases same : n = i.val
    · simp [same]
    · have ne : (⟨n, inside⟩ : Fin 9) ≠ i := fun eq => same (congrArg Fin.val eq)
      simp [putRegister, ne, Ne.symm same]

theorem cutRegister_write_with {α : Type} {filler : List α} {regs : Fin 9 → α}
    {i : Fin 9} {cut : RegisterCut α}
    (found : cutRegister i.val (tapeRegistersWith filler regs) = some cut) (value : α) :
    cut.before ++ cut.last :: value :: cut.after = tapeRegistersWith filler (putRegister regs i value) := by
  have reverse := cut_reversed found
  have index : cut.after.reverse.length = i.val := by simpa using (cutRegister_sound found).2
  have bounded : i.val < (List.ofFn regs).length := by simp
  have wrote := congrArg (fun l : List α => l.set i.val value) reverse
  rw [List.set_append_left _ _ bounded, ← put_ofFn, List.set_append_right _ _ (by rw [index]; exact Nat.le_refl _),
    index, Nat.sub_self, List.set] at wrote
  have same : (tapeRegistersWith filler (putRegister regs i value)).reverse =
      (cut.before ++ cut.last :: value :: cut.after).reverse := by
    rw [tapeRegistersWith_reverse, wrote]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  exact (List.reverse_inj.mp same).symm

theorem cutRegister_value {regs : Registers} {i : Fin 9} {cut : RegisterCut}
    (found : cutRegister i.val (tapeRegisters regs) = some cut) :
    cut.value = regs i := cutRegister_value_with found

theorem cutRegister_write {regs : Registers} {i : Fin 9} {cut : RegisterCut}
    (found : cutRegister i.val (tapeRegisters regs) = some cut) (value : Nat) :
    cut.before ++ cut.last :: value :: cut.after = tapeRegisters (putRegister regs i value) :=
  cutRegister_write_with found value

end I0451.Runtime
