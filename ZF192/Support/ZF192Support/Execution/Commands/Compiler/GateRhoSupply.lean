module
public import ZF192Support.Execution.Commands.Compiler.HeadSupply
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZF192Support.Internal (imp mem eqc all)
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
private lemma E_discard (t w:M) : abstractModelEval modelDISCARD ⟨t,w,0,0⟩=some ⟨0,w,0,0⟩ := by rw [abstractModelEval_eq]; exact modelDISCARD_total t w
private lemma E_J (u w:M) : abstractModelEval (modelJ u) ⟨0,w,0,0⟩=some ⟨0,w,u,0⟩ := by rw [abstractModelEval_eq]; exact modelJ_total u w
private lemma E_pop (t x w d h:M) : abstractModelEval modelPOP ⟨t,modelCantor x w,d,h⟩=some ⟨t,w,0,x⟩ := by rw [abstractModelEval_eq]; exact modelPOP_pair t x w d h
private lemma E_pops (xs:List M) (t w d h:M) : abstractModelEval (modelPOPs (xs.length+1)) ⟨t,(xs++[0]).foldr modelCantor w,d,h⟩=some ⟨t,w,0,0⟩ := by rw [abstractModelEval_eq]; exact modelPOPs_clear xs t w d h
private lemma E_ax (a x y:M) (s:Store M) : abstractModelEval [.ax a x y] s=some ⟨gate a (s.d+x) (s.h+y),(heads a (s.d+x) (s.h+y) s.d s.h++[s.t]).foldr modelCantor s.w,0,0⟩ := by
 rw [abstractModelEval_eq]; rfl
private lemma E_shift8 (a x y t w d h:M) : abstractModelEval ([.ax a x y]++List.replicate 8 .shift) ⟨t,w,d,h⟩=some ⟨axRho8 a (d+x) (h+y) d,modelCantor t w,0,all d h⟩ := by
 rw [abstractModelEval_eq]; exact modelAX_shift8 a x y t w d h
noncomputable def modelSupplyGate (a d h:M) : List (Command M) := modelDISCARD++([.ax a d h]++modelPOPs 9)
noncomputable def modelSupplyRho (a offset h u:M) : List (Command M) := modelDISCARD++(modelJ u++(([.ax a (offset) h]++List.replicate 8 .shift)++modelPOP))
private lemma opaque_supplyGate (a d h t w:M) : abstractModelEval (modelSupplyGate a d h) ⟨t,w,0,0⟩=some ⟨gate a d h,w,0,0⟩ := by
 rw [modelSupplyGate,abstractModelEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractModelEval_append,E_ax]
 simp only [Option.bind_some,zero_add]
 simpa only [heads,implicationHeads, CKernel.Generic.Codes.axImplicationHeads,List.length_append,List.length_singleton,List.length_cons,List.length_nil,Nat.reduceAdd] using E_pops (heads a d h 0 0) (gate a d h) w 0 0
lemma modelSupplyGate_total (a d h t w:M) (had:a≠d) (hah:a≠h) : modelCommandsEval (modelSupplyGate a d h) ⟨t,w,0,0⟩=some ⟨axGate a d h,w,0,0⟩ := by
 rw [←abstractModelEval_eq,opaque_supplyGate]
 unfold gate
 rw [if_pos ⟨had,hah⟩]
private lemma opaque_supplyRho (a offset h u t w:M) : abstractModelEval (modelSupplyRho a offset h u) ⟨t,w,0,0⟩=some ⟨axRho8 a (u + offset) h u,w,0,0⟩ := by
 rw [modelSupplyRho,abstractModelEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractModelEval_append,E_J]
 simp only [Option.bind_some]
 rw [abstractModelEval_append,E_shift8]
 simp only [Option.bind_some,zero_add]
 exact E_pop (axRho8 a (u + offset) h u) 0 w 0 (all u 0)
lemma modelSupplyRho_total (a offset h u t w:M) : modelCommandsEval (modelSupplyRho a offset h u) ⟨t,w,0,0⟩=some ⟨axRho8 a (u + offset) h u,w,0,0⟩ := by
 rw [←abstractModelEval_eq]; exact opaque_supplyRho a offset h u t w
end ZF192Support.ModelCommands
