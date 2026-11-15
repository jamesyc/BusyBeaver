module
public import DirectContextProgramContext
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option synthInstance.maxSize 512

def unaryFormula (kind : Bool) (p : ZFR.Formula) : ZFR.Formula :=
 if kind then .ex p else .all p

theorem agree_unary (kind : Bool) (q : RosserDirect.Label)
    (h : RosserDirect.Append.machine (tokenBits (if kind then 15 else 13)) q ≠ .halt) :
 machine (.unary kind q) = Routine.relocate constructRoles (Control.unary kind)
   (RosserDirect.Append.machine (tokenBits (if kind then 15 else 13)) q) := by
 cases q <;> simp_all [machine,RosserDirect.Append.machine]

theorem agree_moveFormula (q : RosserDirect.Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.moveFormula q) = Routine.relocate moveRoles Control.moveFormula (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem embed_unary (kind : Bool) (q : RosserDirect.Label) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles (Control.unary kind) (RosserDirect.cfg q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.unary kind q) v p vals scr tmp rows := by
 unfold Routine.embed cfg RosserDirect.cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_moveFormula (q : RosserDirect.Label) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.moveFormula (RosserDirect.cfg q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.moveFormula q) v p vals scr tmp rows := by
 unfold Routine.embed cfg RosserDirect.cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem unary_run (kind : Bool) (f : ZFR.Formula) (v : Option Symbol)
    (program src rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.unary kind .scan) v program (Membership.formulaPayload f ++ .frameEnd :: src) [] [] rows)
   (cfg (.unary kind .done) none program src []
     (Membership.formulaPayload (unaryFormula kind f) ++ [.frameEnd]) rows) := by
 have localRun := RosserDirect.Append.append_frame (tokenBits (if kind then 15 else 13))
   (Membership.formulaPayload f) (payloadBits_no_end _) v src []
 have h := Routine.lift_embedded_run constructRoles construct_injective (Control.unary kind)
   (RosserDirect.Append.machine (tokenBits (if kind then 15 else 13))) machine (agree_unary kind)
   (storage program [] [] [] rows) localRun (by simp [RosserDirect.cfg])
 simp only [embed_unary] at h
 cases kind <;> simpa [Membership.formulaPayload,unaryFormula,ZFR.TokenVM.emitFormula,payloadBits,
   List.flatMap_append,List.append_assoc] using h

theorem move_formula_run (f : ZFR.Formula) (v : Option Symbol)
    (program dst rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.moveFormula .scan) v program dst [] (TypedContext.value (.formula f)) rows)
   (cfg (.moveFormula .done) none program (TypedContext.value (.formula f) ++ dst) [] [] rows) := by
 have localRun := RosserDirect.move_frame (payloadBits (valueTokens (.formula f)))
   (payloadBits_no_end _) v [] dst
 have h := Routine.lift_embedded_run moveRoles move_injective Control.moveFormula
   RosserDirect.machine machine agree_moveFormula (storage program [] [] [] rows) localRun (by simp [RosserDirect.cfg])
 simpa [embed_moveFormula,TypedContext.value,valueSymbols] using h



theorem formula_value (f : ZFR.Formula) : TypedContext.value (.formula f) =
 .bit1 :: .tokenEnd :: (Membership.formulaPayload f ++ [.frameEnd]) := by
 have hb : tokenBits 1 = [.bit1,.tokenEnd] := by decide
 simp [TypedContext.value,valueSymbols,valueTokens,payloadBits,Membership.formulaPayload,hb,List.append_assoc]

theorem enter_bottom (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step machine (cfg (.dispatch (.opcode 0)) v p vals scr tmp rows) =
 some (cfg .bottom v p vals scr tmp rows) := rfl

theorem bottom_step (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg .bottom v p vals [] [] rows) =
 some (cfg (.moveFormula .scan) v p vals [] (TypedContext.value (.formula .bot)) rows) := by
 simp [machine,formula_value,Membership.formulaPayload,ZFR.TokenVM.emitFormula,payloadBits,
   tokenBits,bitSymbol,cfg,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem enter_unary (kind : Bool) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step machine (cfg (.dispatch (.opcode (if kind then 7 else 6))) v p vals scr tmp rows) =
 some (cfg (.unaryTag0 kind) v p vals scr tmp rows) := by cases kind <;> rfl

theorem unary_tag0 (kind : Bool) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg (.unaryTag0 kind) v p (.bit1 :: .tokenEnd :: vals) [] [] rows) =
 some (cfg (.unaryTag1 kind) (some .bit1) p (.tokenEnd :: vals) [] [] rows) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem unary_tag1 (kind : Bool) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine (cfg (.unaryTag1 kind) v p (.tokenEnd :: vals) [] [] rows) =
 some (cfg (.unary kind .scan) (some .tokenEnd) p vals [] [] rows) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem leave_unary (kind : Bool) (f : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.step machine
   (cfg (.unary kind .done) v p vals [] (Membership.formulaPayload f ++ [.frameEnd]) rows) =
 some (cfg (.moveFormula .scan) v p vals [] (TypedContext.value (.formula f)) rows) := by
 simp [machine,cfg,TM2.step,TM2.stepAux,storage,formula_value]
 funext k; cases k <;> rfl

theorem leave_moveFormula (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step machine (cfg (.moveFormula .done) v p vals scr tmp rows) =
 some (cfg (.dispatch .start) v p vals scr tmp rows) := rfl

theorem execute_bottom (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits 1 ++ rest) (TypedContext.stack s) [] [] rows)
   (cfg (.dispatch .start) none rest (TypedContext.stack (.formula .bot :: s)) [] [] rows) := by
 obtain ⟨w,hd⟩ := dispatch_run 0 v rest (TypedContext.stack s) [] [] rows
 have he := global_step (enter_bottom w rest (TypedContext.stack s) [] [] rows)
 have hb := global_step (bottom_step w rest (TypedContext.stack s) rows)
 have hm := move_formula_run .bot w rest (TypedContext.stack s) rows
 have hr := global_step (leave_moveFormula none rest (TypedContext.stack (.formula .bot :: s)) [] [] rows)
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hd he hb hm hr ⊢
 exact hd.trans (he.trans (hb.trans (hm.trans hr)))

theorem execute_unary (kind : Bool) (f : ZFR.Formula)
    (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits (if kind then 15 else 13) ++ rest)
     (TypedContext.stack (.formula f :: s)) [] [] rows)
   (cfg (.dispatch .start) none rest
     (TypedContext.stack (.formula (unaryFormula kind f) :: s)) [] [] rows) := by
 obtain ⟨w,hd⟩ := dispatch_run (if kind then 7 else 6) v rest (TypedContext.stack (.formula f :: s)) [] [] rows
 have he := global_step (enter_unary kind w rest (TypedContext.stack (.formula f :: s)) [] [] rows)
 have h0 := global_step (unary_tag0 kind w rest (Membership.formulaPayload f ++ .frameEnd :: TypedContext.stack s) rows)
 have h1 := global_step (unary_tag1 kind (some .bit1) rest (Membership.formulaPayload f ++ .frameEnd :: TypedContext.stack s) rows)
 have hc := unary_run kind f (some .tokenEnd) rest (TypedContext.stack s) rows
 have hl := global_step (leave_unary kind (unaryFormula kind f) none rest (TypedContext.stack s) rows)
 have hm := move_formula_run (unaryFormula kind f) none rest (TypedContext.stack s) rows
 have hr := global_step (leave_moveFormula none rest (TypedContext.stack (.formula (unaryFormula kind f) :: s)) [] [] rows)
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,formula_value,List.append_assoc,List.cons_append,List.singleton_append] at hd he h0 h1 hc hl hm hr ⊢
 have h := hd.trans (he.trans (h0.trans (h1.trans (hc.trans (hl.trans (hm.trans hr))))))
 cases kind <;> exact h



def binaryFormula (kind : Fin 3) (p q : ZFR.Formula) : ZFR.Formula :=
 if kind.val = 0 then .and p q else if kind.val = 1 then .or p q else .imp p q

theorem binary_cases (kind : Fin 3) : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega

theorem agree_binary (kind : Fin 3) (q : RosserDirect.Binary.Control)
    (h : RosserDirect.Binary.machine (7+2*kind.val) q ≠ .halt) :
 machine (.binary kind q) = Routine.relocate constructRoles (Control.binary kind)
   (RosserDirect.Binary.machine (7+2*kind.val) q) := by
 cases q <;> simp_all [machine,RosserDirect.Binary.machine]

theorem embed_binary (kind : Fin 3) (q : RosserDirect.Binary.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles (Control.binary kind) (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.binary kind q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem binary_local (kind : Fin 3) (p q : ZFR.Formula) (v : Option Symbol)
    (src dst : List Symbol) :
 TM2.Reaches (RosserDirect.Binary.machine (7+2*kind.val))
   (config .boot v (TypedContext.value (.formula q) ++ TypedContext.value (.formula p) ++ src) [] dst)
   (config .done none src [] (TypedContext.value (.formula (binaryFormula kind p q)) ++ dst)) := by
 have h := RosserDirect.Binary.assemble (7+2*kind.val)
   (payloadBits (valueTokens (.formula p))) (Membership.formulaPayload q)
   (payloadBits_no_end _) (payloadBits_no_end _) v src dst
 have hb : tokenBits 1 = [.bit1,.tokenEnd] := by decide
 rcases binary_cases kind with rfl | rfl | rfl <;>
   simpa [TypedContext.value,valueSymbols,valueTokens,Membership.formulaPayload,binaryFormula,
     ZFR.TokenVM.emitFormula,payloadBits,List.flatMap_append,List.append_assoc,hb] using h

theorem binary_run (kind : Fin 3) (p q : ZFR.Formula) (v : Option Symbol)
    (program src rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.binary kind .boot) v program (TypedContext.value (.formula q) ++ TypedContext.value (.formula p) ++ src) [] [] rows)
   (cfg (.binary kind .done) none program src [] (TypedContext.value (.formula (binaryFormula kind p q))) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective (Control.binary kind)
   (RosserDirect.Binary.machine (7+2*kind.val)) machine (agree_binary kind)
   (storage program [] [] [] rows) (binary_local kind p q v src []) (by simp [config])
 simpa [embed_binary] using h

theorem enter_binary (kind : Fin 3) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step machine (cfg (.dispatch (.opcode ⟨3+kind.val,by omega⟩)) v p vals scr tmp rows) =
 some (cfg (.binary kind .boot) v p vals scr tmp rows) := by
 rcases binary_cases kind with rfl | rfl | rfl <;> rfl

theorem leave_binary (kind : Fin 3) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step machine (cfg (.binary kind .done) v p vals scr tmp rows) =
 some (cfg (.moveFormula .scan) v p vals scr tmp rows) := rfl

theorem execute_binary (kind : Fin 3) (p q : ZFR.Formula)
    (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits (7+2*kind.val) ++ rest)
     (TypedContext.stack (.formula q :: .formula p :: s)) [] [] rows)
   (cfg (.dispatch .start) none rest
     (TypedContext.stack (.formula (binaryFormula kind p q) :: s)) [] [] rows) := by
 obtain ⟨w,hd⟩ := dispatch_run ⟨3+kind.val,by omega⟩ v rest
   (TypedContext.stack (.formula q :: .formula p :: s)) [] [] rows
 have he := global_step (enter_binary kind w rest (TypedContext.stack (.formula q :: .formula p :: s)) [] [] rows)
 have hc := binary_run kind p q w rest (TypedContext.stack s) rows
 have hl := global_step (leave_binary kind none rest (TypedContext.stack s) [] (TypedContext.value (.formula (binaryFormula kind p q))) rows)
 have hm := move_formula_run (binaryFormula kind p q) none rest (TypedContext.stack s) rows
 have hr := global_step (leave_moveFormula none rest (TypedContext.stack (.formula (binaryFormula kind p q) :: s)) [] [] rows)
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.append_assoc] at hd he hc hl hm hr ⊢
 have h := hd.trans (he.trans (hc.trans (hl.trans (hm.trans hr))))
 have hn : 2*(3+kind.val)+1 = 7+2*kind.val := by omega
 simpa only [hn] using h



theorem agree_nat (q : RosserDirect.Label) (h : NatPayload.machine q ≠ .halt) :
 machine (.natScan q) = Routine.relocate natRoles Control.natScan (NatPayload.machine q) := by
 cases q <;> simp_all [machine,NatPayload.machine]

theorem embed_nat (q : RosserDirect.Label) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed natRoles Control.natScan (RosserDirect.cfg q v p scr tmp) (storage [] vals [] [] rows) =
 cfg (.natScan q) v p vals scr tmp rows := by
 unfold Routine.embed cfg RosserDirect.cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem nat_run (n : Nat) (v : Option Symbol) (rest vals rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.natScan .scan) v (tokenBits n ++ rest) vals [] [] rows)
   (cfg (.natScan .done) none rest vals [] (tokenBits n ++ [.frameEnd]) rows) := by
 have h := Routine.lift_embedded_run natRoles nat_injective Control.natScan
   NatPayload.machine machine agree_nat (storage [] vals [] [] rows)
   (NatPayload.nat_payload n v rest []) (by simp [RosserDirect.cfg])
 simpa only [embed_nat] using h

theorem move_nat_run (n : Nat) (v : Option Symbol) (program dst rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.moveFormula .scan) v program dst [] (TypedContext.value (.nat n)) rows)
   (cfg (.moveFormula .done) none program (TypedContext.value (.nat n) ++ dst) [] [] rows) := by
 have localRun := RosserDirect.move_frame (payloadBits [0,2*n]) (payloadBits_no_end _) v [] dst
 have h := Routine.lift_embedded_run moveRoles move_injective Control.moveFormula
   RosserDirect.machine machine agree_moveFormula (storage program [] [] [] rows) localRun (by simp [RosserDirect.cfg])
 simpa [embed_moveFormula,TypedContext.value,payloadBits,List.append_assoc] using h

theorem dispatch_nat_run (n : Nat) (hn : n ≠ 0) (v : Option Symbol) (rest vals rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits (2*n) ++ rest) vals [] [] rows)
   (cfg (.dispatch .natPayload) (some .bit0) (tokenBits n ++ rest) vals [] [] rows) := by
 have localRun := TypedContext.reach_step (OpcodeDispatch.dispatch_nat_positive n hn v rest [] vals)
 have h := Routine.lift_embedded_run dispatchRoles dispatch_injective Control.dispatch
   OpcodeDispatch.machine machine agree_dispatch (storage [] [] [] [] rows) localRun (by simp [config])
 simpa only [embed_dispatch] using h

theorem dispatch_zero_run (v : Option Symbol) (rest vals rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits 0 ++ rest) vals [] [] rows)
   (cfg (.dispatch .natZero) (some .tokenEnd) rest vals [] [] rows) := by
 have localRun := TypedContext.reach_step (OpcodeDispatch.dispatch_nat_zero v rest [] vals)
 have h := Routine.lift_embedded_run dispatchRoles dispatch_injective Control.dispatch
   OpcodeDispatch.machine machine agree_dispatch (storage [] [] [] [] rows) localRun (by simp [config])
 simpa only [embed_dispatch] using h

theorem enter_nat (v : Option Symbol) (program vals rows : List Symbol) :
 TM2.step machine (cfg (.dispatch .natPayload) v program vals [] [] rows) =
 some (cfg (.natScan .scan) v program vals [] [] rows) := rfl

theorem enter_zero (v : Option Symbol) (program vals rows : List Symbol) :
 TM2.step machine (cfg (.dispatch .natZero) v program vals [] [] rows) =
 some (cfg .natZero v program vals [] [] rows) := rfl

theorem zero_step (v : Option Symbol) (program vals rows : List Symbol) :
 TM2.step machine (cfg .natZero v program vals [] [] rows) =
 some (cfg (.moveFormula .scan) v program vals [] (TypedContext.value (.nat 0)) rows) := by
 simp [machine,TypedContext.value,tokenBits,cfg,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem nat_exit (n : Nat) (hn : n ≠ 0) (v : Option Symbol) (program vals rows : List Symbol) :
 TM2.step machine (cfg (.natScan .done) v program vals [] (tokenBits n ++ [.frameEnd]) rows) =
 some (cfg (.moveFormula .scan) v program vals [] (TypedContext.value (.nat n)) rows) := by
 have hb : (2*n).bits = false :: n.bits := Nat.bit0_bits n hn
 simp [machine,TypedContext.value,tokenBits,hb,bitSymbol,List.append_assoc,cfg,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

/-- All natural payloads are represented without any size bound. Constructor
field storage uses2*n, matching the source VM's emitted natural token. -/
theorem execute_nat (n : Nat) (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits (2*n) ++ rest) (TypedContext.stack s) [] [] rows)
   (cfg (.dispatch .start) none rest (TypedContext.stack (.nat n :: s)) [] [] rows) := by
 by_cases hn : n = 0
 · subst n
   have hd := dispatch_zero_run v rest (TypedContext.stack s) rows
   have he := global_step (enter_zero (some .tokenEnd) rest (TypedContext.stack s) rows)
   have hz := global_step (zero_step (some .tokenEnd) rest (TypedContext.stack s) rows)
   have hm := move_nat_run 0 (some .tokenEnd) rest (TypedContext.stack s) rows
   have hr := global_step (leave_moveFormula none rest (TypedContext.stack (.nat 0 :: s)) [] [] rows)
   simpa [TM2.Reaches,TypedContext.stack] using hd.trans (he.trans (hz.trans (hm.trans hr)))
 · have hd := dispatch_nat_run n hn v rest (TypedContext.stack s) rows
   have he := global_step (enter_nat (some .bit0) (tokenBits n ++ rest) (TypedContext.stack s) rows)
   have hc := nat_run n (some .bit0) rest (TypedContext.stack s) rows
   have hl := global_step (nat_exit n hn none rest (TypedContext.stack s) rows)
   have hm := move_nat_run n none rest (TypedContext.stack s) rows
   have hr := global_step (leave_moveFormula none rest (TypedContext.stack (.nat n :: s)) [] [] rows)
   simpa [TM2.Reaches,TypedContext.stack] using hd.trans (he.trans (hc.trans (hl.trans (hm.trans hr))))



theorem agree_atomic (kind : Bool) (q : AtomicFormula.Control)
    (h : AtomicFormula.machine kind q ≠ .halt) :
 machine (.atomic kind q) = Routine.relocate constructRoles (Control.atomic kind) (AtomicFormula.machine kind q) := by
 cases q <;> simp_all [machine,AtomicFormula.machine]

theorem embed_atomic (kind : Bool) (q : AtomicFormula.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles (Control.atomic kind) (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.atomic kind q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem atomic_run (kind : Bool) (a b : Nat) (v : Option Symbol) (program src rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.atomic kind .tagB) v program (TypedContext.value (.nat b) ++ TypedContext.value (.nat a) ++ src) [] [] rows)
   (cfg (.atomic kind .done) none program src [] (TypedContext.value (.formula (AtomicFormula.formula kind a b))) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective (Control.atomic kind)
   (AtomicFormula.machine kind) machine (agree_atomic kind) (storage program [] [] [] rows)
   (AtomicFormula.construct kind a b v src []) (by simp [config])
 simpa [embed_atomic] using h

theorem enter_atomic (kind : Bool) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step machine (cfg (.dispatch (.opcode (if kind then 2 else 1))) v p vals scr tmp rows) =
 some (cfg (.atomic kind .tagB) v p vals scr tmp rows) := by cases kind <;> rfl

theorem leave_atomic (kind : Bool) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step machine (cfg (.atomic kind .done) v p vals scr tmp rows) =
 some (cfg (.moveFormula .scan) v p vals scr tmp rows) := rfl

theorem execute_atomic (kind : Bool) (a b : Nat)
    (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits (if kind then 5 else 3) ++ rest)
     (TypedContext.stack (.nat b :: .nat a :: s)) [] [] rows)
   (cfg (.dispatch .start) none rest
     (TypedContext.stack (.formula (AtomicFormula.formula kind a b) :: s)) [] [] rows) := by
 obtain ⟨w,hd⟩ := dispatch_run (if kind then 2 else 1) v rest (TypedContext.stack (.nat b :: .nat a :: s)) [] [] rows
 have he := global_step (enter_atomic kind w rest (TypedContext.stack (.nat b :: .nat a :: s)) [] [] rows)
 have hc := atomic_run kind a b w rest (TypedContext.stack s) rows
 have hl := global_step (leave_atomic kind none rest (TypedContext.stack s) [] (TypedContext.value (.formula (AtomicFormula.formula kind a b))) rows)
 have hm := move_formula_run (AtomicFormula.formula kind a b) none rest (TypedContext.stack s) rows
 have hr := global_step (leave_moveFormula none rest (TypedContext.stack (.formula (AtomicFormula.formula kind a b) :: s)) [] [] rows)
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.append_assoc] at hd he hc hl hm hr ⊢
 have h := hd.trans (he.trans (hc.trans (hl.trans (hm.trans hr))))
 cases kind <;> exact h



end RosserDirect.ContextProgram
