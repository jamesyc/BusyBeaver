module
public import DirectImpIntroPremise
@[expose] public section
namespace RosserDirect.FramedRowConstructor
open Turing Segment
set_option backward.isDefEq.respectTransparency false

theorem construct_seq_raw (Γ : ZFR.Context) (p : ZFR.Formula)
 (v : Option Symbol) (src rows : List Symbol) :
 TM2.Reaches (machine false)
 (config (.formula0 0) v (TypedContext.value (.formula p) ++ TypedContext.value (.context Γ) ++ src) [] rows)
 (config .done none src [] (FramedRow.encode (.seq Γ p) ++ rows)) := by
 have h0 := move_formula false 0 p v (TypedContext.value (.context Γ) ++ src) rows
 have h1 := finish_context false Γ none src (FramedRow.formulaFrame p ++ rows)
 simpa [TM2.Reaches,afterFormula,FramedRow.encode,List.append_assoc] using h0.trans h1
end RosserDirect.FramedRowConstructor

namespace RosserDirect.ImpIntroPremise
open Turing Segment
set_option backward.isDefEq.respectTransparency false

theorem cons_raw (p : ZFR.Formula) (Γ : ZFR.Context) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches TypedContext.machine
 (config .context0 v (TypedContext.value (.context Γ) ++ TypedContext.value (.formula p) ++ src) [] dst)
 (config .done none src [] (TypedContext.value (.context (p :: Γ)) ++ dst)) := by
 simpa [TypedContext.value,valueSymbols,valueTokens,Membership.formulaPayload,payloadBits,List.append_assoc] using
   TypedContext.cons_payload p Γ v src dst

theorem construct_raw (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (src dst : List Symbol) :
 TM2.Reaches machine
 (config (.save (.scan (.run 0 .start))) v ((TypedContext.stack [.formula b,.formula a,.context Γ] ++ src)) [] dst)
 (config .done none (FramedRow.encode (.seq (a :: Γ) b) ++ src) [] dst) := by
 have h0 := Routine.lift_embedded_run id Function.injective_id Control.save TypedBlock.moveMachine machine agree_save (fun _ => [])
   (TypedBlock.move_block 0 [.formula b] rfl v ((TypedContext.stack [.formula a,.context Γ] ++ src)) dst) (by simp [config])
 simp only [embed_save] at h0
 have l0 : TM2.Reaches machine
   (config (.save .done) none ((TypedContext.stack [.formula a,.context Γ] ++ src)) [] ((TypedContext.stack [.formula b] ++ dst)))
   (config (.swapIn (.first (.scan (.run 0 .start)))) none ((TypedContext.stack [.formula a,.context Γ] ++ src)) [] ((TypedContext.stack [.formula b] ++ dst))) := Relation.ReflTransGen.single rfl
 have h1 := Routine.lift_embedded_run id Function.injective_id Control.swapIn OperandSwap.machine machine agree_swapIn (fun _ => [])
   (OperandSwap.swap_fields (.context Γ) (.formula a) none src ((TypedContext.stack [.formula b] ++ dst))) (by simp [config])
 simp only [embed_swapIn] at h1
 have l1 : TM2.Reaches machine
   (config (.swapIn .done) none ((TypedContext.stack [.context Γ,.formula a] ++ src)) [] ((TypedContext.stack [.formula b] ++ dst)))
   (config (.cons .context0) none ((TypedContext.stack [.context Γ,.formula a] ++ src)) [] ((TypedContext.stack [.formula b] ++ dst))) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run id Function.injective_id Control.cons TypedContext.machine machine agree_cons (fun _ => [])
   (cons_raw a Γ none src (TypedContext.value (.formula b) ++ dst)) (by simp [config])
 simp only [embed_cons] at h2
 have l2 : TM2.Reaches machine
   (config (.cons .done) none src [] ((TypedContext.stack [.context (a :: Γ),.formula b] ++ dst)))
   (config (.swapOut (.first (.scan (.run 0 .start)))) none src [] ((TypedContext.stack [.context (a :: Γ),.formula b] ++ dst))) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.swapOut OperandSwap.machine machine agree_swapOut (fun _ => [])
   (OperandSwap.swap_fields (.formula b) (.context (a :: Γ)) none dst src) (by simp [config])
 simp only [embed_swapOut] at h3
 have l3 : TM2.Reaches machine
   (config (.swapOut .done) none src [] ((TypedContext.stack [.formula b,.context (a :: Γ)] ++ dst)))
   (config (.row (.formula0 0)) none src [] ((TypedContext.stack [.formula b,.context (a :: Γ)] ++ dst))) := Relation.ReflTransGen.single rfl
 have h4 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.row (FramedRowConstructor.machine false) machine agree_row (fun _ => [])
   (FramedRowConstructor.construct_seq_raw (a :: Γ) b none dst src) (by simp [config])
 simp only [embed_row] at h4
 have l4 : TM2.Reaches machine
   (config (.row .done) none (FramedRow.encode (.seq (a :: Γ) b) ++ src) [] dst)
   (config .done none (FramedRow.encode (.seq (a :: Γ) b) ++ src) [] dst) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 l0 h1 l1 h2 l2 h3 l3 h4 l4 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans (l3.trans (h4.trans l4))))))))


end RosserDirect.ImpIntroPremise
