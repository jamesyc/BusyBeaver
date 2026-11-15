module
public import ModelNativeSource
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeSource
open ZFR.ArithmeticRepresentation M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def oldIndex (j:Fin 9) : Fin 20 := ⟨j.val+2,by omega⟩
def newIndex (j:Fin 9) : Fin 20 := ⟨j.val+11,by omega⟩
def slotGraph (φ:ArithmeticSemisentence 2) (j:Fin 9) : ArithmeticSemisentence 20 :=
 Rew.bind ![Semiterm.bvar (newIndex j),Semiterm.bvar (oldIndex j)] Semiterm.fvar ▹ φ
def allRegs (f:Fin 9→ArithmeticSemisentence 20) : ArithmeticSemisentence 20 :=
 (List.finRange 9).foldr (fun j rest=>f j ⋏ rest) ⊤
lemma allRegs_eval (f:Fin 9→ArithmeticSemisentence 20) (v:Fin 20→M) :
 (allRegs f).Evalb v ↔ ∀j,(f j).Evalb v := by
 have aux (xs:List (Fin 9)) :
  (xs.foldr (fun j rest=>f j ⋏ rest) ⊤).Evalb v ↔ ∀j∈xs,(f j).Evalb v := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]
 simpa [allRegs] using aux (List.finRange 9)
def sameRegs : ArithmeticSemisentence 20 := allRegs (slotGraph “n o. n=o”)
def incRegs (r:Nat) : ArithmeticSemisentence 20 :=
 allRegs (fun j=>slotGraph (if j.val=r then “n o. n=o+1” else “n o. n=o”) j)
def decRegs (r:Nat) : ArithmeticSemisentence 20 :=
 allRegs (fun j=>slotGraph (if j.val=r then predecessorGraph.val else “n o. n=o”) j)
def pcGraph (k:Nat) : ArithmeticSemisentence 20 := “#0=↑k”
def zeroReg (r:Nat) : ArithmeticSemisentence 20 :=
 Rew.bind (fun _:Fin 1=>Semiterm.bvar (oldIndex (registerIndex r))) Semiterm.fvar ▹ (“x. x=0”:ArithmeticSemisentence 1)
def instructionGraph (i:Instruction) : ArithmeticSemisentence 20 :=
 match i with
 | .inc r k => pcGraph k ⋏ incRegs r
 | .dec r z p => (zeroReg r ⋏ pcGraph z ⋏ sameRegs) ⋎ (∼zeroReg r ⋏ pcGraph p ⋏ decRegs r)
 | .jump k => pcGraph k ⋏ sameRegs
 | .halt => ⊥
lemma slotGraph_eval (φ:ArithmeticSemisentence 2) (j:Fin 9) (v:Fin 20→M) :
 (slotGraph φ j).Evalb v ↔ φ.Evalb ![v (newIndex j),v (oldIndex j)] := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [hv,slotGraph,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq]
lemma instructionGraph_eval (i:Instruction) (v:Fin 20→M) :
 (instructionGraph i).Evalb v ↔
 execute i ⟨v 1,fun j=>v (oldIndex j)⟩=some ⟨v 0,fun j=>v (newIndex j)⟩ := by
 have hs : (sameRegs).Evalb v ↔ (fun j=>v (newIndex j))=(fun j=>v (oldIndex j)) := by
  simp [sameRegs,allRegs_eval,slotGraph_eval,funext_iff]
 have hi (r:Nat) : (incRegs r).Evalb v ↔ (fun j=>v (newIndex j))=(fun j=>if j.val=r then v (oldIndex j)+1 else v (oldIndex j)) := by
  simp only [incRegs,allRegs_eval,slotGraph_eval,funext_iff]
  apply forall_congr'; intro j; split <;> simp_all
 have hd (r:Nat) : (decRegs r).Evalb v ↔ (fun j=>v (newIndex j))=(fun j=>if j.val=r then modelPredecessor (v (oldIndex j)) else v (oldIndex j)) := by
  simp only [decRegs,allRegs_eval,slotGraph_eval,funext_iff]
  apply forall_congr'; intro j; split
  · exact predecessorGraph_value _ _
  · simp_all
 have hz (r:Nat) : (zeroReg r).Evalb v ↔ v (oldIndex (registerIndex r))=0 := by
  simp [zeroReg,Semiformula.eval_rew,Function.comp_def,Matrix.empty_eq]
 cases i with
 | inc r k => simp [instructionGraph,pcGraph,hi,execute,numeral_eq_natCast,State.mk.injEq,eq_comm]
 | jump k => simp [instructionGraph,pcGraph,hs,execute,numeral_eq_natCast,State.mk.injEq,eq_comm]
 | halt => simp [instructionGraph,execute]
 | dec r z p =>
   by_cases h:v (oldIndex (registerIndex r))=0 <;>
    simp [instructionGraph,pcGraph,hz,hs,hd,execute,numeral_eq_natCast,State.mk.injEq,h,eq_comm]
end ZF209.NativeSource
