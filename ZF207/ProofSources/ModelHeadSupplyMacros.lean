module
public import ModelAXShift2
public import ModelAXShift3
public import ModelAXShift4
public import ModelAXShift5
public import ModelAXShift6
public import ModelAXShift7
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.ModelCommands
open ZF207.MM0ModelReplay ZFR.ArithmeticRepresentation
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
private lemma E_shift2 (a x y t w d h:M) :
 abstractModelEval ([.ax a x y]++List.replicate 2 .shift) ⟨t,w,d,h⟩ =
 some ⟨t323 a (d+x) (h+y),[t325 a (d+x) (h+y),t326 a (d+x) (h+y),t327 a (d+x) (h+y),t328 a (d+x) (h+y),t329 a (d+x) (h+y) d,t322 d h,t].foldr modelCantor w,0,t324 a (d+x) (h+y)⟩ := by rw [abstractModelEval_eq]; exact modelAX_shift2 a x y t w d h
private lemma E_shift3 (a x y t w d h:M) :
 abstractModelEval ([.ax a x y]++List.replicate 3 .shift) ⟨t,w,d,h⟩ =
 some ⟨t324 a (d+x) (h+y),[t326 a (d+x) (h+y),t327 a (d+x) (h+y),t328 a (d+x) (h+y),t329 a (d+x) (h+y) d,t322 d h,t].foldr modelCantor w,0,t325 a (d+x) (h+y)⟩ := by rw [abstractModelEval_eq]; exact modelAX_shift3 a x y t w d h
private lemma E_shift4 (a x y t w d h:M) :
 abstractModelEval ([.ax a x y]++List.replicate 4 .shift) ⟨t,w,d,h⟩ =
 some ⟨t325 a (d+x) (h+y),[t327 a (d+x) (h+y),t328 a (d+x) (h+y),t329 a (d+x) (h+y) d,t322 d h,t].foldr modelCantor w,0,t326 a (d+x) (h+y)⟩ := by rw [abstractModelEval_eq]; exact modelAX_shift4 a x y t w d h
private lemma E_shift5 (a x y t w d h:M) :
 abstractModelEval ([.ax a x y]++List.replicate 5 .shift) ⟨t,w,d,h⟩ =
 some ⟨t326 a (d+x) (h+y),[t328 a (d+x) (h+y),t329 a (d+x) (h+y) d,t322 d h,t].foldr modelCantor w,0,t327 a (d+x) (h+y)⟩ := by rw [abstractModelEval_eq]; exact modelAX_shift5 a x y t w d h
private lemma E_shift6 (a x y t w d h:M) :
 abstractModelEval ([.ax a x y]++List.replicate 6 .shift) ⟨t,w,d,h⟩ =
 some ⟨t327 a (d+x) (h+y),[t329 a (d+x) (h+y) d,t322 d h,t].foldr modelCantor w,0,t328 a (d+x) (h+y)⟩ := by rw [abstractModelEval_eq]; exact modelAX_shift6 a x y t w d h
private lemma E_shift7 (a x y t w d h:M) :
 abstractModelEval ([.ax a x y]++List.replicate 7 .shift) ⟨t,w,d,h⟩ =
 some ⟨t328 a (d+x) (h+y),[t322 d h,t].foldr modelCantor w,0,t329 a (d+x) (h+y) d⟩ := by rw [abstractModelEval_eq]; exact modelAX_shift7 a x y t w d h
private lemma opaque_modelSupplyHead1_total (a d h t w:M) :
 abstractModelEval (modelSupplyHead 1 a d h) ⟨t,w,0,0⟩=some ⟨t323 a d h,w,0,0⟩ := by
 rw [modelSupplyHead,abstractModelEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractModelEval_append,E_shift2]
 simp only [Option.bind_some,zero_add]
 simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,List.cons_append,List.nil_append] using
  E_pops [t325 a d h,t326 a d h,t327 a d h,t328 a d h,t329 a d h 0,t322 0 0] (t323 a d h) w 0 (t324 a d h)
private lemma opaque_modelSupplyHead2_total (a d h t w:M) :
 abstractModelEval (modelSupplyHead 2 a d h) ⟨t,w,0,0⟩=some ⟨t324 a d h,w,0,0⟩ := by
 rw [modelSupplyHead,abstractModelEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractModelEval_append,E_shift3]
 simp only [Option.bind_some,zero_add]
 simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,List.cons_append,List.nil_append] using
  E_pops [t326 a d h,t327 a d h,t328 a d h,t329 a d h 0,t322 0 0] (t324 a d h) w 0 (t325 a d h)
private lemma opaque_modelSupplyHead3_total (a d h t w:M) :
 abstractModelEval (modelSupplyHead 3 a d h) ⟨t,w,0,0⟩=some ⟨t325 a d h,w,0,0⟩ := by
 rw [modelSupplyHead,abstractModelEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractModelEval_append,E_shift4]
 simp only [Option.bind_some,zero_add]
 simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,List.cons_append,List.nil_append] using
  E_pops [t327 a d h,t328 a d h,t329 a d h 0,t322 0 0] (t325 a d h) w 0 (t326 a d h)
private lemma opaque_modelSupplyHead4_total (a d h t w:M) :
 abstractModelEval (modelSupplyHead 4 a d h) ⟨t,w,0,0⟩=some ⟨t326 a d h,w,0,0⟩ := by
 rw [modelSupplyHead,abstractModelEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractModelEval_append,E_shift5]
 simp only [Option.bind_some,zero_add]
 simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,List.cons_append,List.nil_append] using
  E_pops [t328 a d h,t329 a d h 0,t322 0 0] (t326 a d h) w 0 (t327 a d h)
private lemma opaque_modelSupplyHead5_total (a d h t w:M) :
 abstractModelEval (modelSupplyHead 5 a d h) ⟨t,w,0,0⟩=some ⟨t327 a d h,w,0,0⟩ := by
 rw [modelSupplyHead,abstractModelEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractModelEval_append,E_shift6]
 simp only [Option.bind_some,zero_add]
 simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,List.cons_append,List.nil_append] using
  E_pops [t329 a d h 0,t322 0 0] (t327 a d h) w 0 (t328 a d h)
private lemma opaque_modelSupplyHead6_total (a d h t w:M) :
 abstractModelEval (modelSupplyHead 6 a d h) ⟨t,w,0,0⟩=some ⟨t328 a d h,w,0,0⟩ := by
 rw [modelSupplyHead,abstractModelEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractModelEval_append,E_shift7]
 simp only [Option.bind_some,zero_add]
 simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,List.cons_append,List.nil_append] using
  E_pops [t322 0 0] (t328 a d h) w 0 (t329 a d h 0)

lemma modelSupplyHead1_total (a d h t w:M) :
 modelCommandsEval (modelSupplyHead 1 a d h) ⟨t,w,0,0⟩=some ⟨t323 a d h,w,0,0⟩ := by
 rw [←abstractModelEval_eq]; exact opaque_modelSupplyHead1_total a d h t w
lemma modelSupplyHead2_total (a d h t w:M) :
 modelCommandsEval (modelSupplyHead 2 a d h) ⟨t,w,0,0⟩=some ⟨t324 a d h,w,0,0⟩ := by
 rw [←abstractModelEval_eq]; exact opaque_modelSupplyHead2_total a d h t w
lemma modelSupplyHead3_total (a d h t w:M) :
 modelCommandsEval (modelSupplyHead 3 a d h) ⟨t,w,0,0⟩=some ⟨t325 a d h,w,0,0⟩ := by
 rw [←abstractModelEval_eq]; exact opaque_modelSupplyHead3_total a d h t w
lemma modelSupplyHead4_total (a d h t w:M) :
 modelCommandsEval (modelSupplyHead 4 a d h) ⟨t,w,0,0⟩=some ⟨t326 a d h,w,0,0⟩ := by
 rw [←abstractModelEval_eq]; exact opaque_modelSupplyHead4_total a d h t w
lemma modelSupplyHead5_total (a d h t w:M) :
 modelCommandsEval (modelSupplyHead 5 a d h) ⟨t,w,0,0⟩=some ⟨t327 a d h,w,0,0⟩ := by
 rw [←abstractModelEval_eq]; exact opaque_modelSupplyHead5_total a d h t w
lemma modelSupplyHead6_total (a d h t w:M) :
 modelCommandsEval (modelSupplyHead 6 a d h) ⟨t,w,0,0⟩=some ⟨t328 a d h,w,0,0⟩ := by
 rw [←abstractModelEval_eq]; exact opaque_modelSupplyHead6_total a d h t w
end ZF207.ModelCommands
