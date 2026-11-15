module
public import DirectExistsElimPremises
@[expose] public section
namespace RosserDirect.QuantifierRow
open Turing Segment
set_option backward.isDefEq.respectTransparency false

def quantified (existential : Bool) (f : ZFR.Formula) : ZFR.Formula := if existential then .ex f else .all f
def suffix (existential : Bool) := tokenBits (if existential then 15 else 13)

inductive Q where
 | drop (q : Grammar.DropControl TypedBlock.Control)
 | unary (q : Label) | restore (q : Label) | row (q : FramedRowConstructor.Control) | done
 deriving DecidableEq, Fintype, Inhabited

def machine (existential : Bool) : Q → Stmt Q
 | .drop .done => .goto (fun _ => .unary .scan)
 | .drop q => Routine.relocate id Q.drop (TypedBlock.dropMachine q)
 | .unary .done => .goto (fun _ => .restore .scan)
 | .unary q => Routine.relocate id Q.unary (Append.machine (suffix existential) q)
 | .restore .done => .goto (fun _ => .row (.formula0 0))
 | .restore q => Routine.relocate SelectSecond.swap Q.restore (RosserDirect.machine q)
 | .row .done => .goto (fun _ => .done)
 | .row q => Routine.relocate id Q.row (FramedRowConstructor.machine false q)
 | .done => .halt

theorem agree_drop (e : Bool) (q : Grammar.DropControl TypedBlock.Control) (h : TypedBlock.dropMachine q ≠ .halt) :
 machine e (.drop q) = Routine.relocate id Q.drop (TypedBlock.dropMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]
theorem agree_unary (e : Bool) (q : Label) (h : Append.machine (suffix e) q ≠ .halt) :
 machine e (.unary q) = Routine.relocate id Q.unary (Append.machine (suffix e) q) := by
 cases q <;> simp_all [machine,Append.machine]
theorem agree_restore (e : Bool) (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine e (.restore q) = Routine.relocate SelectSecond.swap Q.restore (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_row (e : Bool) (q : FramedRowConstructor.Control) (h : FramedRowConstructor.machine false q ≠ .halt) :
 machine e (.row q) = Routine.relocate id Q.row (FramedRowConstructor.machine false q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_id {L : Type} (labels : L → Q) (q : L) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id labels (config q v a b c) (fun _ => []) = config (labels q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_swap (q : Label) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Q.restore (config q v a b c) (fun _ => []) = config (.restore q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem unary (e : Bool) (f : ZFR.Formula) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (Append.machine (suffix e))
  (config Label.scan v (TypedContext.value (.formula f) ++ src) [] dst)
  (config Label.done none src [] (TypedContext.value (.formula (quantified e f)) ++ dst)) := by
 have h := Append.append_frame (suffix e) (payloadBits (valueTokens (.formula f))) (payloadBits_no_end _) v src dst
 cases e <;> simpa [TM2.Reaches,cfg,config,TypedContext.value,valueSymbols,valueTokens,ZFR.TokenVM.emitFormula,
   quantified,suffix,payloadBits,List.flatMap_append,List.append_assoc] using h

/-- Universal expected-premise row (false) or existential result row (true).
The unused substitution term is discarded as a complete typed operand. -/
theorem construct (e : Bool) (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat)
 (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (machine e)
  (config (.drop (.scan (.run 0 .start))) v
   (TypedContext.value (.nat t) ++ TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ src) [] dst)
  (config .done none src [] (FramedRow.encode (.seq Γ (quantified e f)) ++ dst)) := by
 obtain ⟨w,hw⟩ := TypedBlock.drop_block 0 [.nat t] rfl v
   (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ src) [] dst
 have h0 := Routine.lift_embedded_run id Function.injective_id Q.drop
   TypedBlock.dropMachine (machine e) (agree_drop e) (fun _ => []) hw (by simp [config])
 simp only [embed_id,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h0
 have l0 : TM2.Reaches (machine e)
   (config (.drop .done) w (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ src) [] dst)
   (config (.unary .scan) w (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ src) [] dst) := Relation.ReflTransGen.single rfl
 have h1 := Routine.lift_embedded_run id Function.injective_id Q.unary
   (Append.machine (suffix e)) (machine e) (agree_unary e) (fun _ => [])
   (unary e f w (TypedContext.value (.context Γ) ++ src) dst) (by simp [config])
 simp only [embed_id] at h1
 have l1 : TM2.Reaches (machine e)
   (config (.unary .done) none (TypedContext.value (.context Γ) ++ src) [] (TypedContext.value (.formula (quantified e f)) ++ dst))
   (config (.restore .scan) none (TypedContext.value (.context Γ) ++ src) [] (TypedContext.value (.formula (quantified e f)) ++ dst)) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Q.restore
   RosserDirect.machine (machine e) (agree_restore e) (fun _ => [])
   (AllIntroPremise.move_formula (quantified e f) none dst (TypedContext.value (.context Γ) ++ src)) (by simp [config])
 simp only [embed_swap] at h2
 have l2 : TM2.Reaches (machine e)
   (config (.restore .done) none (TypedContext.value (.formula (quantified e f)) ++ TypedContext.value (.context Γ) ++ src) [] dst)
   (config (.row (.formula0 0)) none (TypedContext.value (.formula (quantified e f)) ++ TypedContext.value (.context Γ) ++ src) [] dst) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run id Function.injective_id Q.row
   (FramedRowConstructor.machine false) (machine e) (agree_row e) (fun _ => [])
   (FramedRowConstructor.construct_seq_raw Γ (quantified e f) none src dst) (by simp [config])
 simp only [embed_id] at h3
 have l3 : TM2.Reaches (machine e)
   (config (.row .done) none src [] (FramedRow.encode (.seq Γ (quantified e f)) ++ dst))
   (config .done none src [] (FramedRow.encode (.seq Γ (quantified e f)) ++ dst)) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,List.append_assoc] at h0 l0 h1 l1 h2 l2 h3 l3 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans l3))))))

end RosserDirect.QuantifierRow
