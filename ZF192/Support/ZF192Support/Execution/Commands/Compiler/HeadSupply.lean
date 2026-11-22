module
public import ZF192Support.Execution.Commands.Compiler.SupplyHelpers
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZF192Support.Internal (imp mem eqc all)
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def modelSupplyHead (j:Nat) (a d h:M) : List (Command M) :=
 modelDISCARD++(([.ax a d h]++List.replicate (j+1) .shift)++modelPOPs (8-j))
noncomputable opaque certifiedModelEval : {f : List (Command M) → Store M → Option (Store M) //
 ∀ cs s, f cs s = modelCommandsEval cs s} := ⟨modelCommandsEval,fun _ _ => rfl⟩
noncomputable def abstractModelEval := (certifiedModelEval (M:=M)).val
theorem abstractModelEval_eq (cs : List (Command M)) (s : Store M) : abstractModelEval cs s = modelCommandsEval cs s := (certifiedModelEval (M:=M)).property cs s
theorem abstractModelEval_append (xs ys : List (Command M)) (s : Store M) : abstractModelEval (xs++ys) s = (abstractModelEval xs s).bind (abstractModelEval ys) := by
 rw [show abstractModelEval ys = modelCommandsEval ys from funext (abstractModelEval_eq ys)]
 simp only [abstractModelEval_eq,modelCommandsEval_append]
private theorem E_discard (t w:M) : abstractModelEval modelDISCARD ⟨t,w,0,0⟩ = some ⟨0,w,0,0⟩ := by rw [abstractModelEval_eq]; exact modelDISCARD_total t w
private theorem E_pops (xs:List M) (t w d h:M) : abstractModelEval (modelPOPs (xs.length+1)) ⟨t,(xs++[0]).foldr modelCantor w,d,h⟩=some ⟨t,w,0,0⟩ := by rw [abstractModelEval_eq]; exact modelPOPs_clear xs t w d h
/-- The selector numbers heads from one, in the order AX pushes them.
The seventh implication and the final universal code remain available to POP. -/
lemma modelSupplyHead_total (j : Fin 6) (a d h t w : M) :
    modelCommandsEval (modelSupplyHead (j.val + 1) a d h) ⟨t,w,0,0⟩ =
    some ⟨(implicationHeads a d h 0).getD j.val 0,w,0,0⟩ := by
  let stack := implicationHeads a d h 0
  have size : stack.length = 7 := rfl
  have hj : j.val < stack.length := by omega
  have hn : j.val + 1 < stack.length := by omega
  let before := stack.take j.val
  let rest := stack.drop (j.val + 2) ++ [all (0:M) 0]
  have splitStack : stack = before ++ stack[j.val] :: stack[j.val+1] :: stack.drop (j.val+2) := by
    calc
      stack = before ++ stack.drop j.val := (List.take_append_drop _ _).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hj, List.drop_eq_getElem_cons hn]
  have safe : ∀ z ∈ before ++ [stack[j.val]], z ∈ stack := by
    intro z hz
    rw [splitStack]
    rcases List.mem_append.mp hz with hb | hs
    · exact List.mem_append_left _ hb
    · exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hs)))
  have splitHeads : heads a (0+d) (0+h) 0 0 =
      before ++ stack[j.val] :: stack[j.val+1] :: rest := by
    simpa only [heads, zero_add, rest, List.append_assoc, List.cons_append] using
      congrArg (· ++ [all (0:M) 0]) splitStack
  have countShift : before.length + 2 = j.val + 1 + 1 := by
    simp [before, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have countPop : rest.length + 1 = 8 - (j.val + 1) := by
    simp only [rest, List.length_append, List.length_drop, size, List.length_singleton]
    omega
  have shift : abstractModelEval ([.ax a d h] ++ List.replicate (j.val + 1 + 1) .shift)
      ⟨0,w,0,0⟩ = some ⟨stack[j.val],(rest ++ [0]).foldr modelCantor w,0,stack[j.val+1]⟩ := by
    rw [abstractModelEval_eq, ← countShift]
    exact modelAX_select a d h 0 w 0 0 before _ _ rest splitHeads (by simpa only [zero_add] using safe)
  have value : (implicationHeads a d h 0).getD j.val 0 = stack[j.val] := by
    change stack.getD j.val 0 = stack[j.val]
    rw [List.getD_eq_getElem?_getD, getElem?_pos stack j.val hj]
    rfl
  rw [← abstractModelEval_eq, modelSupplyHead, abstractModelEval_append, E_discard]
  simp only [Option.bind_some]
  rw [abstractModelEval_append, shift, ← countPop, value]
  exact E_pops rest stack[j.val] w 0 stack[j.val+1]

end ZF192Support.ModelCommands
