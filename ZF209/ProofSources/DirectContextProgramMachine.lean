module
public import DirectRoutineRelabel
public import DirectBinaryConstructors
public import DirectNatPayload
public import DirectAtomicFormula
public import DirectFramedRowCopy
public import DirectTypedBlockCopy
public import DirectTypedBlockDrop
public import DirectSelectSecond
public import DirectPeirceConstructor
public import DirectImpIntroPremise
public import DirectConjPremises
public import DirectImpElimPremises
public import DirectBranchPremises
public import DirectDisjElimPremises
public import DirectWeakeningContextCheck
public import DirectQuantifierRow
public import DirectSubstitutionRow
public import DirectExistsElimPremises
public import DirectAllIntroPremise
public import DirectFourStackLink
public import DirectRowPairEquality
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option synthInstance.maxSize 512

def moveMachine : TypedContext.Control → Stmt TypedContext.Control
 | .context0 => TypedContext.expect .bit0 .context1 .reject
 | .context1 => TypedContext.expect .bit1 .context2 .reject
 | .context2 => TypedContext.expect .tokenEnd .entry .reject
 | .entry => FramedContext.entryStmt .scan .flushTail .reject true
 | .scan => scanStmt .scan .entry .reject [.frameEnd]
 | .flushTail => flushStmt .flushTail .tag
 | .tag => TypedContext.tagOutput .done
 | _ => .halt

theorem move_context (Γ : ZFR.Context) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches moveMachine
   (config .context0 v (TypedContext.value (.context Γ) ++ src) [] dst)
   (config .done none src [] (TypedContext.value (.context Γ) ++ dst)) := by
 have h0 := TypedContext.expect_step moveMachine .context0 .context1 .reject .bit0 rfl v
   (.bit1 :: .tokenEnd :: (FramedContext.encode Γ ++ src)) [] dst
 have h1 := TypedContext.expect_step moveMachine .context1 .context2 .reject .bit1 rfl (some .bit0)
   (.tokenEnd :: (FramedContext.encode Γ ++ src)) [] dst
 have h2 := TypedContext.expect_step moveMachine .context2 .entry .reject .tokenEnd rfl (some .bit1)
   (FramedContext.encode Γ ++ src) [] dst
 have ht := (TypedContext.reach_step h0).trans ((TypedContext.reach_step h1).trans (TypedContext.reach_step h2))
 have hc := FramedContext.transfer_context moveMachine .entry .scan .flushTail .tag .reject true
   rfl rfl rfl Γ (some .tokenEnd) src dst
 have he : TM2.step moveMachine
   (config .tag none src [] (Membership.contextFrames Γ ++ [.frameEnd] ++ dst)) =
   some (config .done none src [] (TypedContext.value (.context Γ) ++ dst)) := by
   simp [moveMachine, TypedContext.tagOutput, TypedContext.value, FramedContext.encode,
     config, TM2.step, TM2.stepAux, storage, tokenBits,List.append_assoc]
   funext k; cases k <;> rfl
 have hb : tokenBits 2 = [.bit0,.bit1,.tokenEnd] := by decide
 simpa [TM2.Reaches, TypedContext.value, hb,List.append_assoc] using
   ht.trans (hc.trans (TypedContext.reach_step he))

inductive GlobalStack where
 | program | values | scratch | temporary | rows
 deriving DecidableEq, Fintype, Inhabited
inductive Control where
 | dispatch (q : OpcodeDispatch.Control)
 | construct (q : TypedContext.Control)
 | move (q : TypedContext.Control)
 | bottom | unaryTag0 (kind : Bool) | unaryTag1 (kind : Bool)
 | unary (kind : Bool) (q : RosserDirect.Label)
 | moveFormula (q : RosserDirect.Label)
 | binary (kind : Fin 3) (q : RosserDirect.Binary.Control)
 | natScan (q : RosserDirect.Label) | natZero
 | atomic (kind : Bool) (q : AtomicFormula.Control)
 | proofRow (q : FramedRowConstructor.Control) | proofCopy (q : FramedRowCopy.Control)
 | proofPrepare (q : FramedContext.Control) | proofMember (q : RosserDirect.Membership.Control)
 | proofPopTag | proofDropTarget | proofClear | proofReject
 | expCopy (q : Grammar.CopyControl TypedBlock.Control) | expDrop | expBottom
 | expExpected (q : FramedRowConstructor.Control)
 | expCompare (q : FramedRowEquality.Control) | expResult (q : FramedRowConstructor.Control)
 | diCopy (q : Grammar.CopyControl TypedBlock.Control)
 | diDrop (q : Grammar.DropControl TypedBlock.Control)
 | diExpected (q : FramedRowConstructor.Control) | diCompare (q : FramedRowEquality.Control)
 | diBinary (q : RosserDirect.Binary.Control) | diMove (q : RosserDirect.Label)
 | diResult (q : FramedRowConstructor.Control)
 | ceCopy (q : Grammar.CopyControl TypedBlock.Control)
 | ceBinary (q : RosserDirect.Binary.Control) | ceMove (q : RosserDirect.Label)
 | ceExpected (q : FramedRowConstructor.Control) | ceCompare (q : FramedRowEquality.Control)
 | ceDrop (q : Grammar.DropControl TypedBlock.Control)
 | di2Copy (q : Grammar.CopyControl TypedBlock.Control)
 | di2Select (q : SelectSecond.Control)
 | ce2Copy (q : Grammar.CopyControl TypedBlock.Control)
 | ce2Binary (q : RosserDirect.Binary.Control) | ce2Move (q : RosserDirect.Label)
 | ce2Expected (q : FramedRowConstructor.Control) | ce2Compare (q : FramedRowEquality.Control)
 | ce2Select (q : SelectSecond.Control)
 | pc (q : Peirce.Control)
 | iiCopy (q : Grammar.CopyControl TypedBlock.Control)
 | iiBuild (q : ImpIntroPremise.Control)
 | iiCompare (q : FramedRowEquality.Control)
 | iiBinary (q : Binary.Control)
 | ciCopy (q : Grammar.CopyControl TypedBlock.Control)
 | ciBuild (q : ConjPremises.Control)
 | ciCompare (q : RowPairEquality.Control)
 | ciBinary (q : Binary.Control)
 | ieCopy (q : Grammar.CopyControl TypedBlock.Control)
 | ieBuild (q : ImpElimPremises.Control)
 | ieCompare (q : RowPairEquality.Control)
 | ieSelect (q : SelectSecond.Control)
 | bpCopy (q : Grammar.CopyControl TypedBlock.Control)
 | bpBuild (q : BranchPremises.Control)
 | bpCompare (q : RowPairEquality.Control)
 | bpResult (q : FramedRowConstructor.Control)
 | deCopy (q : Grammar.CopyControl TypedBlock.Control)
 | deBuild (q : DisjElimPremises.Control)
 | deCompare (q : RowPairEquality.Control)
 | deSelectB (q : SelectSecond.Control) | deSelectA (q : SelectSecond.Control)
 | wkCopy (q : Grammar.CopyControl TypedBlock.Control)
 | wkSelect (q : SelectSecond.Control)
 | wkExpected (q : FramedRowConstructor.Control)
 | wkCompare (q : FramedRowEquality.Control)
 | wkCheck (q : WeakeningContextCheck.Control)
 | wkResult (q : FramedRowConstructor.Control)
 | wkDrop (q : Grammar.DropControl TypedBlock.Control)
 | aiCopy (q : Grammar.CopyControl TypedBlock.Control)
 | aiBuild (q : AllIntroPremise.Q)
 | aiCompare (q : FramedRowEquality.Control)
 | aiTag0 | aiTag1 | aiUnary (q : RosserDirect.Label)
 | aiMove (q : RosserDirect.Label)
 | aiResult (q : FramedRowConstructor.Control)
 | eeCopy (q : Grammar.CopyControl TypedBlock.Control)
 | eeBuild (q : ExistsElimPremises.Q)
 | eeCompare (q : RowPairEquality.Control)
 | eeSelect (q : SelectSecond.Control)
 | eeResult (q : FramedRowConstructor.Control)
 | qeCopy (exIntro : Bool) (q : Grammar.CopyControl TypedBlock.Control)
 | qeSubst (expected : Bool) (q : SubstitutionRow.Q)
 | qeUnary (expected : Bool) (q : QuantifierRow.Q)
 | qeCompare (exIntro : Bool) (q : FramedRowEquality.Control)
 | unsupported
 deriving DecidableEq, Fintype, Inhabited

abbrev GlobalStmt := TM2.Stmt (fun _ : GlobalStack => Symbol) Control (Option Symbol)
def dispatchRoles : Stack → GlobalStack
 | .input => .program | .scratch => .scratch | .output => .values
def constructRoles : Stack → GlobalStack
 | .input => .values | .scratch => .scratch | .output => .temporary
def moveRoles : Stack → GlobalStack
 | .input => .temporary | .scratch => .scratch | .output => .values

def natRoles : Stack → GlobalStack
 | .input => .program | .scratch => .scratch | .output => .temporary

def rowRoles : Stack → GlobalStack
 | .input => .values | .scratch => .scratch | .output => .rows
def premiseRoles : Stack → GlobalStack
 | .input => .temporary | .scratch => .scratch | .output => .rows

def copyRoles : Stack → GlobalStack
 | .input => .rows | .scratch => .scratch | .output => .values

theorem premise_injective : Function.Injective premiseRoles := by intro a b h; cases a <;> cases b <;> simp_all [premiseRoles]

theorem row_injective : Function.Injective rowRoles := by intro a b h; cases a <;> cases b <;> simp_all [rowRoles]
theorem copy_injective : Function.Injective copyRoles := by intro a b h; cases a <;> cases b <;> simp_all [copyRoles]

theorem nat_injective : Function.Injective natRoles := by intro a b h; cases a <;> cases b <;> simp_all [natRoles]

theorem dispatch_injective : Function.Injective dispatchRoles := by intro a b h; cases a <;> cases b <;> simp_all [dispatchRoles]
theorem construct_injective : Function.Injective constructRoles := by intro a b h; cases a <;> cases b <;> simp_all [constructRoles]
theorem move_injective : Function.Injective moveRoles := by intro a b h; cases a <;> cases b <;> simp_all [moveRoles]

def quantResultRoles : FourStack.K → GlobalStack
 | .stream => .program | .data => .values | .scratch => .scratch | .output => .rows
theorem quantResult_injective : Function.Injective quantResultRoles := by
 intro a b h; cases a <;> cases b <;> simp_all [quantResultRoles]

def quantPremiseRoles : FourStack.K → GlobalStack
 | .stream => .program | .data => .temporary | .scratch => .scratch | .output => .values
theorem quantPremise_injective : Function.Injective quantPremiseRoles := by
 intro a b h; cases a <;> cases b <;> simp_all [quantPremiseRoles]

/-- End-to-end interpreter for syntax constructor opcodes0..9 and natural tokens.
The remaining proof/witness opcode entries are explicitly unsupported. Program, values, scratch and temporary
storage coexist; constructor returns are wired back to token dispatch. -/
def machine : Control → GlobalStmt
 | .dispatch (.opcode n) =>
   if n.val = 0 then .goto (fun _ => .bottom)
   else if n.val = 1 then .goto (fun _ => .atomic false .tagB)
   else if n.val = 2 then .goto (fun _ => .atomic true .tagB)
   else if n.val = 3 then .goto (fun _ => .binary 0 .boot)
   else if n.val = 4 then .goto (fun _ => .binary 1 .boot)
   else if n.val = 5 then .goto (fun _ => .binary 2 .boot)
   else if n.val = 6 then .goto (fun _ => .unaryTag0 false)
   else if n.val = 7 then .goto (fun _ => .unaryTag0 true)
   else if n.val = 8 then .goto (fun _ => .construct .empty)
   else if n.val = 9 then .goto (fun _ => .construct .context0)
   else if n.val = 10 then .goto (fun _ => .proofRow (.formula0 0))
   else if n.val = 22 then .goto (fun _ => .wkCopy (.scan (.run 2 .start)))
   else if n.val = 24 then .goto (fun _ => .qeCopy false (.scan (.run 2 .start)))
   else if n.val = 25 then .goto (fun _ => .qeCopy true (.scan (.run 2 .start)))
   else if n.val = 26 then .goto (fun _ => .eeCopy (.scan (.run 2 .start)))
   else if n.val = 23 then .goto (fun _ => .aiCopy (.scan (.run 1 .start)))
   else if n.val = 21 then .goto (fun _ => .deCopy (.scan (.run 3 .start)))
   else if n.val = 20 then .goto (fun _ => .bpCopy (.scan (.run 3 .start)))
   else if n.val = 13 then .goto (fun _ => .ieCopy (.scan (.run 2 .start)))
   else if n.val = 15 then .goto (fun _ => .ciCopy (.scan (.run 2 .start)))
   else if n.val = 12 then .goto (fun _ => .iiCopy (.scan (.run 2 .start)))
   else if n.val = 11 then .goto (fun _ => .pc (.copy0 (.scan (.run 1 .start))))
   else if n.val = 14 then .goto (fun _ => .expCopy (.scan (.run 1 .start)))
   else if n.val = 17 then .goto (fun _ => .ce2Copy (.scan (.run 2 .start)))
   else if n.val = 16 then .goto (fun _ => .ceCopy (.scan (.run 2 .start)))
   else if n.val = 19 then .goto (fun _ => .di2Copy (.scan (.run 2 .start)))
   else if n.val = 18 then .goto (fun _ => .diCopy (.scan (.run 2 .start)))
   else .goto (fun _ => .unsupported)
 | .qeCopy false .done => .goto (fun _ => .qeUnary true (.drop (.scan (.run 0 .start))))
 | .qeCopy true .done => .goto (fun _ => .qeSubst true (.swap (.first (.scan (.run 0 .start)))))
 | .qeCopy k q => Routine.relocate constructRoles (Control.qeCopy k) (TypedBlock.machine q)
 | .qeUnary true .done => .goto (fun _ => .qeCompare false .tag)
 | .qeUnary false .done => .goto (fun _ => .dispatch .start)
 | .qeUnary k q => Routine.relocate (if k then moveRoles else rowRoles) (Control.qeUnary k) (QuantifierRow.machine (!k) q)
 | .qeSubst true .done => .goto (fun _ => .qeCompare true .tag)
 | .qeSubst false .done => .goto (fun _ => .dispatch .start)
 | .qeSubst k q => Routine.relocate (if k then quantPremiseRoles else quantResultRoles) (Control.qeSubst k) (SubstitutionRow.machine q)
 | .qeCompare k .equal => .goto (fun _ => if k then .qeUnary false (.drop (.scan (.run 0 .start))) else .qeSubst false (.swap (.first (.scan (.run 0 .start)))))
 | .qeCompare _ .different => .goto (fun _ => .proofReject)
 | .qeCompare k q => Routine.relocate rowRoles (Control.qeCompare k) (FramedRowEquality.machine q)
 | .eeCopy .done => .goto (fun _ => .eeBuild (.copy (.scan (.run 2 .start))))
 | .eeCopy q => Routine.relocate constructRoles Control.eeCopy (TypedBlock.machine q)
 | .eeBuild .done => .goto (fun _ => .eeCompare (.first .tag))
 | .eeBuild q => Routine.relocate quantPremiseRoles Control.eeBuild (ExistsElimPremises.machine q)
 | .eeCompare .equal => .goto (fun _ => .eeSelect (.save .scan))
 | .eeCompare .different => .goto (fun _ => .proofReject)
 | .eeCompare q => Routine.relocate rowRoles Control.eeCompare (RowPairEquality.machine q)
 | .eeSelect .done => .goto (fun _ => .eeResult (.formula0 0))
 | .eeSelect q => Routine.relocate constructRoles Control.eeSelect (SelectSecond.machine q)
 | .eeResult .done => .goto (fun _ => .dispatch .start)
 | .eeResult q => Routine.relocate rowRoles Control.eeResult (FramedRowConstructor.machine false q)
 | .aiCopy .done => .goto (fun _ => .aiBuild (.save .scan))
 | .aiCopy q => Routine.relocate constructRoles Control.aiCopy (TypedBlock.machine q)
 | .aiBuild .done => .goto (fun _ => .aiCompare .tag)
 | .aiBuild q => Routine.relocate quantPremiseRoles Control.aiBuild (AllIntroPremise.machine q)
 | .aiCompare .equal => .goto (fun _ => .aiTag0)
 | .aiCompare .different => .goto (fun _ => .proofReject)
 | .aiCompare q => Routine.relocate rowRoles Control.aiCompare (FramedRowEquality.machine q)
 | .aiTag0 => .pop .values (fun _ x => x)
    (.branch (fun x => x == some .bit1) (.goto (fun _ => .aiTag1)) (.goto (fun _ => .proofReject)))
 | .aiTag1 => .pop .values (fun _ x => x)
    (.branch (fun x => x == some .tokenEnd) (.goto (fun _ => .aiUnary .scan)) (.goto (fun _ => .proofReject)))
 | .aiUnary .done => .push .temporary (fun _ => .tokenEnd)
    (.push .temporary (fun _ => .bit1) (.goto (fun _ => .aiMove .scan)))
 | .aiUnary q => Routine.relocate constructRoles Control.aiUnary (RosserDirect.Append.machine (tokenBits 13) q)
 | .aiMove .done => .goto (fun _ => .aiResult (.formula0 0))
 | .aiMove q => Routine.relocate moveRoles Control.aiMove (RosserDirect.machine q)
 | .aiResult .done => .goto (fun _ => .dispatch .start)
 | .aiResult q => Routine.relocate rowRoles Control.aiResult (FramedRowConstructor.machine false q)
 | .dispatch .natPayload => .goto (fun _ => .natScan .scan)
 | .dispatch .natZero => .goto (fun _ => .natZero)
 | .dispatch q => Routine.relocate dispatchRoles Control.dispatch (OpcodeDispatch.machine q)
 | .construct .done => .goto (fun _ => .move .context0)
 | .construct q => Routine.relocate constructRoles Control.construct (TypedContext.machine q)
 | .move .done => .goto (fun _ => .dispatch .start)
 | .move q => Routine.relocate moveRoles Control.move (moveMachine q)
 | .bottom => .push .temporary (fun _ => .frameEnd)
    (.push .temporary (fun _ => .tokenEnd) (.push .temporary (fun _ => .bit1)
      (.push .temporary (fun _ => .tokenEnd) (.push .temporary (fun _ => .bit1)
        (.goto (fun _ => .moveFormula .scan))))))
 | .unaryTag0 kind => .pop .values (fun _ x => x)
    (.branch (fun x => x == some .bit1) (.goto (fun _ => .unaryTag1 kind)) (.goto (fun _ => .unsupported)))
 | .unaryTag1 kind => .pop .values (fun _ x => x)
    (.branch (fun x => x == some .tokenEnd) (.goto (fun _ => .unary kind .scan)) (.goto (fun _ => .unsupported)))
 | .unary kind .done => .push .temporary (fun _ => .tokenEnd)
    (.push .temporary (fun _ => .bit1) (.goto (fun _ => .moveFormula .scan)))
 | .unary kind q => Routine.relocate constructRoles (Control.unary kind)
    (RosserDirect.Append.machine (tokenBits (if kind then 15 else 13)) q)
 | .moveFormula .done => .goto (fun _ => .dispatch .start)
 | .moveFormula q => Routine.relocate moveRoles Control.moveFormula (RosserDirect.machine q)
 | .binary kind .done => .goto (fun _ => .moveFormula .scan)
 | .binary kind q => Routine.relocate constructRoles (Control.binary kind)
    (RosserDirect.Binary.machine (7+2*kind.val) q)
 | .natScan .done => .push .temporary (fun _ => .bit0)
    (.push .temporary (fun _ => .tokenEnd) (.goto (fun _ => .moveFormula .scan)))
 | .natScan q => Routine.relocate natRoles Control.natScan (NatPayload.machine q)
 | .natZero => .push .temporary (fun _ => .frameEnd)
    (.push .temporary (fun _ => .tokenEnd) (.push .temporary (fun _ => .tokenEnd)
      (.goto (fun _ => .moveFormula .scan))))
 | .atomic kind .done => .goto (fun _ => .moveFormula .scan)
 | .atomic kind q => Routine.relocate constructRoles (Control.atomic kind) (AtomicFormula.machine kind q)
 | .proofRow .done => .goto (fun _ => .proofCopy (.scan .tag))
 | .proofRow q => Routine.relocate rowRoles Control.proofRow (FramedRowConstructor.machine false q)
 | .proofCopy .done => .goto (fun _ => .proofPopTag)
 | .proofCopy q => Routine.relocate copyRoles Control.proofCopy (FramedRowCopy.machine q)
 | .proofPopTag => .pop .values (fun _ x => x)
    (.branch (fun x => x == some .bit0) (.goto (fun _ => .proofPrepare .entry)) (.goto (fun _ => .proofReject)))
 | .proofPrepare .done => .goto (fun _ => .proofMember .next)
 | .proofPrepare q => Routine.relocate constructRoles Control.proofPrepare (FramedContext.prepare q)
 | .proofMember .found => .goto (fun _ => .proofDropTarget)
 | .proofMember .absent | .proofMember .reject => .goto (fun _ => .proofReject)
 | .proofMember q => Routine.relocate constructRoles Control.proofMember (RosserDirect.Membership.machine q)
 | .proofDropTarget => .pop .values (fun _ x => x)
    (.branch Option.isNone (.goto (fun _ => .proofReject))
      (.branch (fun x => x == some .frameEnd) (.goto (fun _ => .proofClear)) (.goto (fun _ => .proofDropTarget))))
 | .proofClear => .pop .temporary (fun _ x => x)
    (.branch Option.isNone (.goto (fun _ => .dispatch .start)) (.goto (fun _ => .proofClear)))
 | .expCopy .done => .goto (fun _ => .expDrop)
 | .expCopy q => Routine.relocate constructRoles Control.expCopy (TypedBlock.machine q)
 | .expDrop => .pop .temporary (fun _ x => x)
    (.branch Option.isNone (.goto (fun _ => .proofReject))
      (.branch (fun x => x == some .frameEnd) (.goto (fun _ => .expBottom)) (.goto (fun _ => .expDrop))))
 | .expBottom => .push .temporary (fun _ => .frameEnd)
    (.push .temporary (fun _ => .tokenEnd) (.push .temporary (fun _ => .bit1)
      (.push .temporary (fun _ => .tokenEnd) (.push .temporary (fun _ => .bit1)
        (.goto (fun _ => .expExpected (.formula0 0)))))))
 | .expExpected .done => .goto (fun _ => .expCompare .tag)
 | .expExpected q => Routine.relocate moveRoles Control.expExpected (FramedRowConstructor.machine false q)
 | .expCompare .equal => .goto (fun _ => .expResult (.formula0 0))
 | .expCompare .different => .goto (fun _ => .proofReject)
 | .expCompare q => Routine.relocate rowRoles Control.expCompare (FramedRowEquality.machine q)
 | .expResult .done => .goto (fun _ => .dispatch .start)
 | .expResult q => Routine.relocate rowRoles Control.expResult (FramedRowConstructor.machine false q)
 | .diCopy .done => .goto (fun _ => .diDrop (.scan (.run 0 .start)))
 | .diCopy q => Routine.relocate constructRoles Control.diCopy (TypedBlock.machine q)
 | .diDrop .done => .goto (fun _ => .diExpected (.formula0 0))
 | .diDrop q => Routine.relocate moveRoles Control.diDrop (TypedBlock.dropMachine q)
 | .diExpected .done => .goto (fun _ => .diCompare .tag)
 | .diExpected q => Routine.relocate moveRoles Control.diExpected (FramedRowConstructor.machine false q)
 | .diCompare .equal => .goto (fun _ => .diBinary .boot)
 | .diCompare .different => .goto (fun _ => .proofReject)
 | .diCompare q => Routine.relocate rowRoles Control.diCompare (FramedRowEquality.machine q)
 | .diBinary .done => .goto (fun _ => .diMove .scan)
 | .diBinary q => Routine.relocate constructRoles Control.diBinary (RosserDirect.Binary.machine 9 q)
 | .diMove .done => .goto (fun _ => .diResult (.formula0 0))
 | .diMove q => Routine.relocate moveRoles Control.diMove (RosserDirect.machine q)
 | .diResult .done => .goto (fun _ => .dispatch .start)
 | .diResult q => Routine.relocate rowRoles Control.diResult (FramedRowConstructor.machine false q)
 | .ceCopy .done => .goto (fun _ => .ceBinary .boot)
 | .ceCopy q => Routine.relocate constructRoles Control.ceCopy (TypedBlock.machine q)
 | .ceBinary .done => .goto (fun _ => .ceMove .scan)
 | .ceBinary q => Routine.relocate moveRoles Control.ceBinary (RosserDirect.Binary.machine 7 q)
 | .ceMove .done => .goto (fun _ => .ceExpected (.formula0 0))
 | .ceMove q => Routine.relocate constructRoles Control.ceMove (RosserDirect.machine q)
 | .ceExpected .done => .goto (fun _ => .ceCompare .tag)
 | .ceExpected q => Routine.relocate moveRoles Control.ceExpected (FramedRowConstructor.machine false q)
 | .ceCompare .equal => .goto (fun _ => .ceDrop (.scan (.run 0 .start)))
 | .ceCompare .different => .goto (fun _ => .proofReject)
 | .ceCompare q => Routine.relocate rowRoles Control.ceCompare (FramedRowEquality.machine q)
 | .ceDrop .done => .goto (fun _ => .diResult (.formula0 0))
 | .ceDrop q => Routine.relocate constructRoles Control.ceDrop (TypedBlock.dropMachine q)
 | .di2Copy .done => .goto (fun _ => .di2Select (.save .scan))
 | .di2Copy q => Routine.relocate constructRoles Control.di2Copy (TypedBlock.machine q)
 | .di2Select .done => .goto (fun _ => .diExpected (.formula0 0))
 | .di2Select q => Routine.relocate moveRoles Control.di2Select (SelectSecond.machine q)
 | .ce2Copy .done => .goto (fun _ => .ce2Binary .boot)
 | .ce2Copy q => Routine.relocate constructRoles Control.ce2Copy (TypedBlock.machine q)
 | .ce2Binary .done => .goto (fun _ => .ce2Move .scan)
 | .ce2Binary q => Routine.relocate moveRoles Control.ce2Binary (RosserDirect.Binary.machine 7 q)
 | .ce2Move .done => .goto (fun _ => .ce2Expected (.formula0 0))
 | .ce2Move q => Routine.relocate constructRoles Control.ce2Move (RosserDirect.machine q)
 | .ce2Expected .done => .goto (fun _ => .ce2Compare .tag)
 | .ce2Expected q => Routine.relocate moveRoles Control.ce2Expected (FramedRowConstructor.machine false q)
 | .ce2Compare .equal => .goto (fun _ => .ce2Select (.save .scan))
 | .ce2Compare .different => .goto (fun _ => .proofReject)
 | .ce2Compare q => Routine.relocate rowRoles Control.ce2Compare (FramedRowEquality.machine q)
 | .ce2Select .done => .goto (fun _ => .diResult (.formula0 0))
 | .ce2Select q => Routine.relocate constructRoles Control.ce2Select (SelectSecond.machine q)
 | .pc .done => .goto (fun _ => .diMove .scan)
 | .pc q => Routine.relocate constructRoles Control.pc (Peirce.machine q)
 | .iiCopy .done => .goto (fun _ => .iiBuild (.save (.scan (.run 0 .start))))
 | .iiCopy q => Routine.relocate constructRoles Control.iiCopy (TypedBlock.machine q)
 | .iiBuild .done => .goto (fun _ => .iiCompare .tag)
 | .iiBuild q => Routine.relocate moveRoles Control.iiBuild (ImpIntroPremise.machine q)
 | .iiCompare .equal => .goto (fun _ => .iiBinary .boot)
 | .iiCompare .different => .goto (fun _ => .proofReject)
 | .iiCompare q => Routine.relocate premiseRoles Control.iiCompare (FramedRowEquality.machine q)
 | .iiBinary .done => .goto (fun _ => .diMove .scan)
 | .iiBinary q => Routine.relocate constructRoles Control.iiBinary (Binary.machine 11 q)
 | .ciCopy .done => .goto (fun _ => .ciBuild (.copy (.scan (.run 2 .start))))
 | .ciCopy q => Routine.relocate constructRoles Control.ciCopy (TypedBlock.machine q)
 | .ciBuild .done => .goto (fun _ => .ciCompare (.first .tag))
 | .ciBuild q => Routine.relocate moveRoles Control.ciBuild (ConjPremises.machine q)
 | .ciCompare .equal => .goto (fun _ => .ciBinary .boot)
 | .ciCompare .different => .goto (fun _ => .proofReject)
 | .ciCompare q => Routine.relocate rowRoles Control.ciCompare (RowPairEquality.machine q)
 | .ciBinary .done => .goto (fun _ => .diMove .scan)
 | .ciBinary q => Routine.relocate constructRoles Control.ciBinary (Binary.machine 7 q)
 | .ieCopy .done => .goto (fun _ => .ieBuild (.copy (.scan (.run 1 .start))))
 | .ieCopy q => Routine.relocate constructRoles Control.ieCopy (TypedBlock.machine q)
 | .ieBuild .done => .goto (fun _ => .ieCompare (.first .tag))
 | .ieBuild q => Routine.relocate moveRoles Control.ieBuild (ImpElimPremises.machine q)
 | .ieCompare .equal => .goto (fun _ => .ieSelect (.save .scan))
 | .ieCompare .different => .goto (fun _ => .proofReject)
 | .ieCompare q => Routine.relocate rowRoles Control.ieCompare (RowPairEquality.machine q)
 | .ieSelect .done => .goto (fun _ => .diResult (.formula0 0))
 | .ieSelect q => Routine.relocate constructRoles Control.ieSelect (SelectSecond.machine q)
 | .bpCopy .done => .goto (fun _ => .bpBuild (.copy (.scan (.run 3 .start))))
 | .bpCopy q => Routine.relocate constructRoles Control.bpCopy (TypedBlock.machine q)
 | .bpBuild .done => .goto (fun _ => .bpCompare (.first .tag))
 | .bpBuild q => Routine.relocate moveRoles Control.bpBuild (BranchPremises.machine q)
 | .bpCompare .equal => .goto (fun _ => .bpResult (.formula0 2))
 | .bpCompare .different => .goto (fun _ => .proofReject)
 | .bpCompare q => Routine.relocate rowRoles Control.bpCompare (RowPairEquality.machine q)
 | .bpResult .done => .goto (fun _ => .dispatch .start)
 | .bpResult q => Routine.relocate rowRoles Control.bpResult (FramedRowConstructor.machine true q)
 | .deCopy .done => .goto (fun _ => .deBuild (.copy (.scan (.run 3 .start))))
 | .deCopy q => Routine.relocate constructRoles Control.deCopy (TypedBlock.machine q)
 | .deBuild .done => .goto (fun _ => .deCompare (.first .tag))
 | .deBuild q => Routine.relocate moveRoles Control.deBuild (DisjElimPremises.machine q)
 | .deCompare .equal => .goto (fun _ => .deSelectB (.save .scan))
 | .deCompare .different => .goto (fun _ => .proofReject)
 | .deCompare q => Routine.relocate rowRoles Control.deCompare (RowPairEquality.machine q)
 | .deSelectB .done => .goto (fun _ => .deSelectA (.save .scan))
 | .deSelectB q => Routine.relocate constructRoles Control.deSelectB (SelectSecond.machine q)
 | .deSelectA .done => .goto (fun _ => .diResult (.formula0 0))
 | .deSelectA q => Routine.relocate constructRoles Control.deSelectA (SelectSecond.machine q)
 | .wkCopy .done => .goto (fun _ => .wkSelect (.save .scan))
 | .wkCopy q => Routine.relocate constructRoles Control.wkCopy (TypedBlock.machine q)
 | .wkSelect .done => .goto (fun _ => .wkExpected (.formula0 0))
 | .wkSelect q => Routine.relocate moveRoles Control.wkSelect (SelectSecond.machine q)
 | .wkExpected .done => .goto (fun _ => .wkCompare .tag)
 | .wkExpected q => Routine.relocate moveRoles Control.wkExpected (FramedRowConstructor.machine false q)
 | .wkCompare .equal => .goto (fun _ => .wkCheck (.copy (.scan (.run 2 .start))))
 | .wkCompare .different => .goto (fun _ => .proofReject)
 | .wkCompare q => Routine.relocate rowRoles Control.wkCompare (FramedRowEquality.machine q)
 | .wkCheck .accept => .goto (fun _ => .wkResult (.formula0 0))
 | .wkCheck .reject => .goto (fun _ => .proofReject)
 | .wkCheck q => Routine.relocate constructRoles Control.wkCheck (WeakeningContextCheck.machine q)
 | .wkResult .done => .goto (fun _ => .wkDrop (.scan (.run 0 .start)))
 | .wkResult q => Routine.relocate rowRoles Control.wkResult (FramedRowConstructor.machine false q)
 | .wkDrop .done => .load (fun _ => none) (.goto (fun _ => .dispatch .start))
 | .wkDrop q => Routine.relocate constructRoles Control.wkDrop (TypedBlock.dropMachine q)
 | .proofReject | .unsupported => .halt

def storage (program values scratch temporary rows : List Symbol) : GlobalStack → List Symbol
 | .program => program | .values => values | .scratch => scratch | .temporary => temporary | .rows => rows

def cfg (q : Control) (v : Option Symbol) (program values scratch temporary rows : List Symbol) :=
 (⟨some q,v,storage program values scratch temporary rows⟩ : TM2.Cfg (fun _ : GlobalStack => Symbol) Control (Option Symbol))

end RosserDirect.ContextProgram
