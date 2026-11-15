module
public import DirectFourStack
@[expose] public section
namespace RosserDirect.ShiftTraversal
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

inductive Q where
 | prepare (q : ReverseTokens.Q) | seed | next | dispatch (q : OpcodeDispatch.Control)
 | bot (q : Grammar.DropControl TypedBlock.Control)
 | binary (q : ReturnValue.Q (Grammar.CopyControl TypedBlock.Control))
 | binder (q : ReturnValue.Q (TypedNatUnary.Control BinarySuccessor.Q))
 | atomic (q : ReturnValue.Q (Grammar.CopyControl TypedBlock.Control))
 | readNat (second : Bool) (q : Label)
 | shiftNat (second : Bool) (q : ShiftIndex.Q)
 | unframe (second : Bool) (q : NatUnframe.Q)
 | finishData | finishStream | done | reject
 deriving DecidableEq, Fintype, Inhabited

def pushOut : List Symbol → Stmt4 Q → Stmt4 Q
 | [], s => s
 | x :: xs, s => pushOut xs (.push .output (fun _ => x) s)

def destination (op : Nat) : Q :=
 if op = 0 then .bot (.scan (.run 0 .start))
 else if op = 1 ∨ op = 2 then .atomic (.first (.scan (.run 0 .start)))
 else if op = 3 ∨ op = 4 ∨ op = 5 then .binary (.first (.scan (.run 0 .start)))
 else if op = 6 ∨ op = 7 then .binder (.first .start)
 else .reject

def machine : Q → Stmt4 Q
 | .prepare .done => .goto (fun _ => .seed)
 | .prepare q => Routine.relocate prepareRoles Q.prepare (ReverseTokens.machine q)
 | .seed => .push .data (fun _ => .frameEnd)
   (.push .data (fun _ => .frameEnd)
    (.push .data (fun _ => .tokenEnd)
     (.push .data (fun _ => .tokenEnd)
      (.push .output (fun _ => .frameEnd) (.goto (fun _ => .next))))))
 | .next => .peek .data (fun _ x => x)
   (.branch (fun x => x == some .frameEnd) (.goto (fun _ => .finishData))
    (.goto (fun _ => .dispatch .start)))
 | .dispatch (.opcode op) => pushOut (tokenBits (2*op.val+1)) (.goto (fun _ => destination op.val))
 | .dispatch q => Routine.relocate readRoles Q.dispatch (OpcodeDispatch.machine q)
 | .bot .done => .load (fun _ => none) (.goto (fun _ => .next))
 | .bot q => Routine.relocate dataRoles Q.bot (TypedBlock.dropMachine q)
 | .binary .done => .goto (fun _ => .next)
 | .binary q => Routine.relocate dataRoles Q.binary (ReturnValue.duplicateMachine q)
 | .binder .done => .goto (fun _ => .next)
 | .binder q => Routine.relocate dataRoles Q.binder (ReturnValue.incrementMachine q)
 | .atomic .done => .goto (fun _ => .readNat false .scan)
 | .atomic q => Routine.relocate dataRoles Q.atomic (ReturnValue.duplicateMachine q)
 | .readNat second .done => .push .data (fun _ => .tokenEnd)
   (.goto (fun _ => .shiftNat second (.copy (.scan (.run 1 .start)))))
 | .readNat second q => Routine.relocate readRoles (Q.readNat second) (NatPayload.machine q)
 | .shiftNat second .done => .goto (fun _ => .unframe second .tag)
 | .shiftNat second q => Routine.relocate dataRoles (Q.shiftNat second) (ShiftIndex.machine q)
 | .unframe true .done => .goto (fun _ => .next)
 | .unframe false .done => .goto (fun _ => .readNat true .scan)
 | .unframe second q => Routine.relocate outputRoles (Q.unframe second) (NatUnframe.machine q)
 | .finishData => .pop .data (fun _ x => x)
   (.branch (fun x => x == some .frameEnd) (.goto (fun _ => .finishStream)) (.goto (fun _ => .reject)))
 | .finishStream => .pop .stream (fun _ x => x)
   (.branch (fun x => x == some .frameEnd)
    (.push .output (fun _ => .tokenEnd) (.push .output (fun _ => .bit1)
     (.load (fun _ => none) (.goto (fun _ => .done)))))
    (.goto (fun _ => .reject)))
 | .done | .reject => .halt

theorem pushOut_correct (w : List Symbol) (s : Stmt4 Q) (v : Option Symbol) (p a b c : List Symbol) :
 TM2.stepAux (pushOut w s) v (store4 p a b c) = TM2.stepAux s v (store4 p a b (w ++ c)) := by
 induction w generalizing s c with
 | nil => rfl
 | cons x xs ih =>
   rw [pushOut,ih]
   simp only [TM2.stepAux]
   have hu : Function.update (store4 p a b (xs ++ c)) K.output (x :: (xs ++ c)) =
      store4 p a b (x :: (xs ++ c)) := by funext k; cases k <;> rfl
   change TM2.stepAux s v (Function.update (store4 p a b (xs ++ c)) K.output (x :: (xs ++ c))) = _
   rw [hu]
   rfl

theorem agree_prepare (q : ReverseTokens.Q) (h : ReverseTokens.machine q ≠ .halt) :
 machine (.prepare q) = Routine.relocate prepareRoles Q.prepare (ReverseTokens.machine q) := by
 cases q <;> simp_all [machine,ReverseTokens.machine]
theorem agree_dispatch (q : OpcodeDispatch.Control) (h : OpcodeDispatch.machine q ≠ .halt) :
 machine (.dispatch q) = Routine.relocate readRoles Q.dispatch (OpcodeDispatch.machine q) := by
 cases q <;> simp_all [machine,OpcodeDispatch.machine,OpcodeDispatch.active]
theorem agree_bot (q : Grammar.DropControl TypedBlock.Control) (h : TypedBlock.dropMachine q ≠ .halt) :
 machine (.bot q) = Routine.relocate dataRoles Q.bot (TypedBlock.dropMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]
theorem agree_binary (q : ReturnValue.Q (Grammar.CopyControl TypedBlock.Control)) (h : ReturnValue.duplicateMachine q ≠ .halt) :
 machine (.binary q) = Routine.relocate dataRoles Q.binary (ReturnValue.duplicateMachine q) := by
 cases q <;> simp_all [machine,ReturnValue.duplicateMachine,ReturnValue.machine]
theorem agree_binder (q : ReturnValue.Q (TypedNatUnary.Control BinarySuccessor.Q)) (h : ReturnValue.incrementMachine q ≠ .halt) :
 machine (.binder q) = Routine.relocate dataRoles Q.binder (ReturnValue.incrementMachine q) := by
 cases q <;> simp_all [machine,ReturnValue.incrementMachine,ReturnValue.machine]
theorem agree_atomic (q : ReturnValue.Q (Grammar.CopyControl TypedBlock.Control)) (h : ReturnValue.duplicateMachine q ≠ .halt) :
 machine (.atomic q) = Routine.relocate dataRoles Q.atomic (ReturnValue.duplicateMachine q) := by
 cases q <;> simp_all [machine,ReturnValue.duplicateMachine,ReturnValue.machine]
theorem agree_read (second : Bool) (q : Label) (h : NatPayload.machine q ≠ .halt) :
 machine (.readNat second q) = Routine.relocate readRoles (Q.readNat second) (NatPayload.machine q) := by
 cases q <;> simp_all [machine,NatPayload.machine]
theorem agree_shift (second : Bool) (q : ShiftIndex.Q) (h : ShiftIndex.machine q ≠ .halt) :
 machine (.shiftNat second q) = Routine.relocate dataRoles (Q.shiftNat second) (ShiftIndex.machine q) := by
 cases q <;> simp_all [machine,ShiftIndex.machine]
theorem agree_unframe (second : Bool) (q : NatUnframe.Q) (h : NatUnframe.machine q ≠ .halt) :
 machine (.unframe second q) = Routine.relocate outputRoles (Q.unframe second) (NatUnframe.machine q) := by
 cases q <;> cases second <;> simp_all [machine,NatUnframe.machine]

theorem next_depth (d : Nat) (v : Option Symbol) (p a s c : List Symbol) :
 TM2.step machine (cfg4 .next v p (TypedContext.value (.nat d) ++ a) s c) =
 some (cfg4 (.dispatch .start) (some .tokenEnd) p (TypedContext.value (.nat d) ++ a) s c) := by
 simp [machine,cfg4,TM2.step,TM2.stepAux,store4,TypedContext.value,tokenBits,Nat.zero_bits]

theorem dispatch_emit (op : Fin 42) (v : Option Symbol) (p a s c : List Symbol) :
 TM2.step machine (cfg4 (.dispatch (.opcode op)) v p a s c) =
 some (cfg4 (destination op.val) v p a s (tokenBits (2*op.val+1) ++ c)) := by
 simp [machine,cfg4,TM2.step,pushOut_correct,TM2.stepAux]

theorem root (op : Fin 42) (d : Nat) (v : Option Symbol) (p a c : List Symbol) :
 ∃ w, TM2.Reaches machine
  (cfg4 .next v (tokenBits (2*op.val+1) ++ p) (TypedContext.value (.nat d) ++ a) [] c)
  (cfg4 (destination op.val) w p (TypedContext.value (.nat d) ++ a) [] (tokenBits (2*op.val+1) ++ c)) := by
 have h0 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (next_depth d v (tokenBits (2*op.val+1) ++ p) a [] c)
 obtain ⟨w,hw⟩ := OpcodeDispatch.dispatch_opcode op (some .tokenEnd) p [] (TypedContext.value (.nat d) ++ a)
 have h1 := Routine.lift_embedded_run readRoles read_injective Q.dispatch
   OpcodeDispatch.machine machine agree_dispatch (fun _ => c) hw (by simp [config])
 simp only [embed_read] at h1
 have h2 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
   (dispatch_emit op w p (TypedContext.value (.nat d) ++ a) [] c)
 exact ⟨w,h0.trans (h1.trans h2)⟩


def afterIndex (second : Bool) : Q := if second then .next else .readNat true .scan

theorem index (second : Bool) (d i : Nat) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.readNat second .scan) v (tokenBits (2*i) ++ p) (TypedContext.value (.nat d) ++ a) [] c)
  (cfg4 (afterIndex second) none p a [] (tokenBits (2*ZFR.sourceShiftIndex d i) ++ c)) := by
 have hn : TM2.Reaches NatPayload.machine
   (config Label.scan v (tokenBits (2*i) ++ p) [] (TypedContext.value (.nat d) ++ a))
   (config Label.done none p [] (tokenBits (2*i) ++ .frameEnd :: (TypedContext.value (.nat d) ++ a))) :=
   NatPayload.nat_payload (2*i) v p (TypedContext.value (.nat d) ++ a)
 have h0 := Routine.lift_embedded_run readRoles read_injective (Q.readNat second)
   NatPayload.machine machine (agree_read second) (fun _ => c) hn (by simp [config])
 simp only [embed_read] at h0
 have h1 : TM2.Reaches machine
   (cfg4 (.readNat second .done) none p (tokenBits (2*i) ++ .frameEnd :: (TypedContext.value (.nat d) ++ a)) [] c)
   (cfg4 (.shiftNat second (.copy (.scan (.run 1 .start)))) none p
     (TypedContext.value (.nat i) ++ TypedContext.value (.nat d) ++ a) [] c) := by
   apply Relation.ReflTransGen.single
   simp [machine,cfg4,TM2.step,TM2.stepAux,store4,TypedContext.value,tokenBits,Nat.zero_bits,List.append_assoc,Function.update]
   funext k; cases k <;> rfl
 have h2 := Routine.lift_embedded_run dataRoles data_injective (Q.shiftNat second)
   ShiftIndex.machine machine (agree_shift second) (fun _ => p)
   (ShiftIndex.shift_index d i none a c) (by simp [config])
 simp only [embed_data] at h2
 have h3 : TM2.Reaches machine
   (cfg4 (.shiftNat second .done) none p a [] (TypedContext.value (.nat (ZFR.sourceShiftIndex d i)) ++ c))
   (cfg4 (.unframe second .tag) none p a [] (TypedContext.value (.nat (ZFR.sourceShiftIndex d i)) ++ c)) := Relation.ReflTransGen.single rfl
 have h4 := Routine.lift_embedded_run outputRoles output_injective (Q.unframe second)
   NatUnframe.machine machine (agree_unframe second) (fun _ => p)
   (NatUnframe.unframe (ZFR.sourceShiftIndex d i) none c a) (by simp [config])
 simp only [embed_output] at h4
 have h5 : TM2.Reaches machine
   (cfg4 (.unframe second .done) none p a [] (tokenBits (2*ZFR.sourceShiftIndex d i) ++ c))
   (cfg4 (afterIndex second) none p a [] (tokenBits (2*ZFR.sourceShiftIndex d i) ++ c)) := by
   apply Relation.ReflTransGen.single
   cases second <;> rfl
 exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))

theorem atomic_indices (d i j : Nat) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.atomic (.first (.scan (.run 0 .start)))) v (tokenBits (2*j) ++ tokenBits (2*i) ++ p)
    (TypedContext.value (.nat d) ++ a) [] c)
  (cfg4 .next none p a [] (tokenBits (2*ZFR.sourceShiftIndex d i) ++ tokenBits (2*ZFR.sourceShiftIndex d j) ++ c)) := by
 have h0 := Routine.lift_embedded_run dataRoles data_injective Q.atomic
   ReturnValue.duplicateMachine machine agree_atomic (fun _ => tokenBits (2*j) ++ tokenBits (2*i) ++ p)
   (ReturnValue.duplicate (.nat d) v a c) (by simp [config])
 simp only [embed_data] at h0
 have h1 : TM2.Reaches machine
   (cfg4 (.atomic .done) none (tokenBits (2*j) ++ tokenBits (2*i) ++ p)
    (TypedContext.value (.nat d) ++ TypedContext.value (.nat d) ++ a) [] c)
   (cfg4 (.readNat false .scan) none (tokenBits (2*j) ++ tokenBits (2*i) ++ p)
    (TypedContext.value (.nat d) ++ TypedContext.value (.nat d) ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h2 := index false d j none (tokenBits (2*i) ++ p) (TypedContext.value (.nat d) ++ a) c
 have h3 := index true d i none p a (tokenBits (2*ZFR.sourceShiftIndex d j) ++ c)
 simp only [TM2.Reaches,afterIndex,Bool.false_eq_true,↓reduceIte,List.append_assoc] at h0 h1 h2 h3 ⊢
 exact h0.trans (h1.trans (h2.trans h3))



theorem drop_depth (d : Nat) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine (cfg4 (.bot (.scan (.run 0 .start))) v p (TypedContext.value (.nat d) ++ a) [] c)
  (cfg4 .next none p a [] c) := by
 obtain ⟨w,hw⟩ := TypedBlock.drop_block 0 [.nat d] rfl v a [] c
 have h0 := Routine.lift_embedded_run dataRoles data_injective Q.bot
   TypedBlock.dropMachine machine agree_bot (fun _ => p) hw (by simp [config])
 simp only [embed_data,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h0
 have h1 : TM2.Reaches machine (cfg4 (.bot .done) w p a [] c) (cfg4 .next none p a [] c) := Relation.ReflTransGen.single rfl
 exact h0.trans h1

theorem duplicate_depth (d : Nat) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine (cfg4 (.binary (.first (.scan (.run 0 .start)))) v p (TypedContext.value (.nat d) ++ a) [] c)
  (cfg4 .next none p (TypedContext.value (.nat d) ++ TypedContext.value (.nat d) ++ a) [] c) := by
 have h0 := Routine.lift_embedded_run dataRoles data_injective Q.binary
   ReturnValue.duplicateMachine machine agree_binary (fun _ => p)
   (ReturnValue.duplicate (.nat d) v a c) (by simp [config])
 simp only [embed_data] at h0
 have h1 : TM2.Reaches machine
   (cfg4 (.binary .done) none p (TypedContext.value (.nat d) ++ TypedContext.value (.nat d) ++ a) [] c)
   (cfg4 .next none p (TypedContext.value (.nat d) ++ TypedContext.value (.nat d) ++ a) [] c) := Relation.ReflTransGen.single rfl
 exact h0.trans h1

theorem increment_depth (d : Nat) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine (cfg4 (.binder (.first .start)) v p (TypedContext.value (.nat d) ++ a) [] c)
  (cfg4 .next none p (TypedContext.value (.nat (d+1)) ++ a) [] c) := by
 have h0 := Routine.lift_embedded_run dataRoles data_injective Q.binder
   ReturnValue.incrementMachine machine agree_binder (fun _ => p)
   (ReturnValue.increment d v a c) (by simp [config])
 simp only [embed_data] at h0
 have h1 : TM2.Reaches machine
   (cfg4 (.binder .done) none p (TypedContext.value (.nat (d+1)) ++ a) [] c)
   (cfg4 .next none p (TypedContext.value (.nat (d+1)) ++ a) [] c) := Relation.ReflTransGen.single rfl
 exact h0.trans h1

def rev (f : ZFR.Formula) := payloadBits (ZFR.TokenVM.emitFormula f).reverse
def forward (f : ZFR.Formula) := payloadBits (ZFR.TokenVM.emitFormula f)
def shifted (d : Nat) (f : ZFR.Formula) := ZFR.rename (ZFR.sourceShiftIndex d) f

/-- Complete binder-aware recursive shift traversal on arbitrary formulas.
The stack of depth jobs is binary encoded and stored in tape data, not labels. -/
theorem traverse (f : ZFR.Formula) (d : Nat) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 .next v (rev f ++ p) (TypedContext.value (.nat d) ++ a) [] c)
  (cfg4 .next none p a [] (forward (shifted d f) ++ c)) := by
 induction f generalizing d v p a c with
 | bot =>
   obtain ⟨w,h0⟩ := root 0 d v p a c
   change TM2.Reaches machine (cfg4 .next v (tokenBits 1 ++ p) (TypedContext.value (.nat d) ++ a) [] c)
     (cfg4 (.bot (.scan (.run 0 .start))) w p (TypedContext.value (.nat d) ++ a) [] (tokenBits 1 ++ c)) at h0
   have h1 := drop_depth d w p a (tokenBits 1 ++ c)
   simpa [TM2.Reaches,rev,forward,shifted,ZFR.rename,ZFR.TokenVM.emitFormula,payloadBits] using h0.trans h1
 | mem i j =>
   obtain ⟨w,h0⟩ := root 1 d v (tokenBits (2*j) ++ tokenBits (2*i) ++ p) a c
   change TM2.Reaches machine
     (cfg4 .next v (tokenBits 3 ++ (tokenBits (2*j) ++ tokenBits (2*i) ++ p)) (TypedContext.value (.nat d) ++ a) [] c)
     (cfg4 (.atomic (.first (.scan (.run 0 .start)))) w (tokenBits (2*j) ++ tokenBits (2*i) ++ p)
      (TypedContext.value (.nat d) ++ a) [] (tokenBits 3 ++ c)) at h0
   have h1 := atomic_indices d i j w p a (tokenBits 3 ++ c)
   simpa [TM2.Reaches,rev,forward,shifted,ZFR.rename,ZFR.TokenVM.emitFormula,ZFR.TokenVM.emitNat,payloadBits,List.append_assoc] using h0.trans h1
 | eq i j =>
   obtain ⟨w,h0⟩ := root 2 d v (tokenBits (2*j) ++ tokenBits (2*i) ++ p) a c
   change TM2.Reaches machine
     (cfg4 .next v (tokenBits 5 ++ (tokenBits (2*j) ++ tokenBits (2*i) ++ p)) (TypedContext.value (.nat d) ++ a) [] c)
     (cfg4 (.atomic (.first (.scan (.run 0 .start)))) w (tokenBits (2*j) ++ tokenBits (2*i) ++ p)
      (TypedContext.value (.nat d) ++ a) [] (tokenBits 5 ++ c)) at h0
   have h1 := atomic_indices d i j w p a (tokenBits 5 ++ c)
   simpa [TM2.Reaches,rev,forward,shifted,ZFR.rename,ZFR.TokenVM.emitFormula,ZFR.TokenVM.emitNat,payloadBits,List.append_assoc] using h0.trans h1
 | and f g ihf ihg =>
   obtain ⟨w,h0⟩ := root 3 d v (rev g ++ rev f ++ p) a c
   change TM2.Reaches machine
     (cfg4 .next v (tokenBits 7 ++ (rev g ++ rev f ++ p)) (TypedContext.value (.nat d) ++ a) [] c)
     (cfg4 (.binary (.first (.scan (.run 0 .start)))) w (rev g ++ rev f ++ p)
      (TypedContext.value (.nat d) ++ a) [] (tokenBits 7 ++ c)) at h0
   have h1 := duplicate_depth d w (rev g ++ rev f ++ p) a (tokenBits 7 ++ c)
   have h2 := ihg d none (rev f ++ p) (TypedContext.value (.nat d) ++ a) (tokenBits 7 ++ c)
   have h3 := ihf d none p a (forward (shifted d g) ++ tokenBits 7 ++ c)
   simp only [TM2.Reaches,List.append_assoc] at h0 h1 h2 h3
   have h := h0.trans (h1.trans (h2.trans h3))
   simpa [TM2.Reaches,rev,forward,shifted,ZFR.rename,ZFR.TokenVM.emitFormula,payloadBits,List.reverse_append,List.flatMap_append,List.append_assoc] using h
 | or f g ihf ihg =>
   obtain ⟨w,h0⟩ := root 4 d v (rev g ++ rev f ++ p) a c
   change TM2.Reaches machine
     (cfg4 .next v (tokenBits 9 ++ (rev g ++ rev f ++ p)) (TypedContext.value (.nat d) ++ a) [] c)
     (cfg4 (.binary (.first (.scan (.run 0 .start)))) w (rev g ++ rev f ++ p)
      (TypedContext.value (.nat d) ++ a) [] (tokenBits 9 ++ c)) at h0
   have h1 := duplicate_depth d w (rev g ++ rev f ++ p) a (tokenBits 9 ++ c)
   have h2 := ihg d none (rev f ++ p) (TypedContext.value (.nat d) ++ a) (tokenBits 9 ++ c)
   have h3 := ihf d none p a (forward (shifted d g) ++ tokenBits 9 ++ c)
   simp only [TM2.Reaches,List.append_assoc] at h0 h1 h2 h3
   have h := h0.trans (h1.trans (h2.trans h3))
   simpa [TM2.Reaches,rev,forward,shifted,ZFR.rename,ZFR.TokenVM.emitFormula,payloadBits,List.reverse_append,List.flatMap_append,List.append_assoc] using h
 | imp f g ihf ihg =>
   obtain ⟨w,h0⟩ := root 5 d v (rev g ++ rev f ++ p) a c
   change TM2.Reaches machine
     (cfg4 .next v (tokenBits 11 ++ (rev g ++ rev f ++ p)) (TypedContext.value (.nat d) ++ a) [] c)
     (cfg4 (.binary (.first (.scan (.run 0 .start)))) w (rev g ++ rev f ++ p)
      (TypedContext.value (.nat d) ++ a) [] (tokenBits 11 ++ c)) at h0
   have h1 := duplicate_depth d w (rev g ++ rev f ++ p) a (tokenBits 11 ++ c)
   have h2 := ihg d none (rev f ++ p) (TypedContext.value (.nat d) ++ a) (tokenBits 11 ++ c)
   have h3 := ihf d none p a (forward (shifted d g) ++ tokenBits 11 ++ c)
   simp only [TM2.Reaches,List.append_assoc] at h0 h1 h2 h3
   have h := h0.trans (h1.trans (h2.trans h3))
   simpa [TM2.Reaches,rev,forward,shifted,ZFR.rename,ZFR.TokenVM.emitFormula,payloadBits,List.reverse_append,List.flatMap_append,List.append_assoc] using h
 | all f ih =>
   obtain ⟨w,h0⟩ := root 6 d v (rev f ++ p) a c
   change TM2.Reaches machine
     (cfg4 .next v (tokenBits 13 ++ (rev f ++ p)) (TypedContext.value (.nat d) ++ a) [] c)
     (cfg4 (.binder (.first .start)) w (rev f ++ p)
      (TypedContext.value (.nat d) ++ a) [] (tokenBits 13 ++ c)) at h0
   have h1 := increment_depth d w (rev f ++ p) a (tokenBits 13 ++ c)
   have h2 := ih (d+1) none p a (tokenBits 13 ++ c)
   have h := h0.trans (h1.trans h2)
   simpa [TM2.Reaches,rev,forward,shifted,ZFR.rename,ZFR.sourceShiftIndex_lift,ZFR.TokenVM.emitFormula,payloadBits,List.reverse_append,List.flatMap_append,List.append_assoc] using h
 | ex f ih =>
   obtain ⟨w,h0⟩ := root 7 d v (rev f ++ p) a c
   change TM2.Reaches machine
     (cfg4 .next v (tokenBits 15 ++ (rev f ++ p)) (TypedContext.value (.nat d) ++ a) [] c)
     (cfg4 (.binder (.first .start)) w (rev f ++ p)
      (TypedContext.value (.nat d) ++ a) [] (tokenBits 15 ++ c)) at h0
   have h1 := increment_depth d w (rev f ++ p) a (tokenBits 15 ++ c)
   have h2 := ih (d+1) none p a (tokenBits 15 ++ c)
   have h := h0.trans (h1.trans h2)
   simpa [TM2.Reaches,rev,forward,shifted,ZFR.rename,ZFR.sourceShiftIndex_lift,ZFR.TokenVM.emitFormula,payloadBits,List.reverse_append,List.flatMap_append,List.append_assoc] using h


theorem seed_step (v : Option Symbol) (p a c : List Symbol) :
 TM2.step machine (cfg4 .seed v p a [] c) =
 some (cfg4 .next v p (TypedContext.value (.nat 0) ++ .frameEnd :: a) [] (.frameEnd :: c)) := by
 simp [machine,cfg4,TM2.step,TM2.stepAux,store4,TypedContext.value,tokenBits,Nat.zero_bits,Function.update]
 funext k; cases k <;> rfl

theorem finish (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 .next none (.frameEnd :: p) (.frameEnd :: a) [] c)
  (cfg4 .done none p a [] (.bit1 :: .tokenEnd :: c)) := by
 have h0 : TM2.Reaches machine
   (cfg4 .next none (.frameEnd :: p) (.frameEnd :: a) [] c)
   (cfg4 .finishData (some .frameEnd) (.frameEnd :: p) (.frameEnd :: a) [] c) := by
   apply Relation.ReflTransGen.single
   simp [machine,cfg4,TM2.step,TM2.stepAux,store4]
 have h1 : TM2.Reaches machine
   (cfg4 .finishData (some .frameEnd) (.frameEnd :: p) (.frameEnd :: a) [] c)
   (cfg4 .finishStream (some .frameEnd) (.frameEnd :: p) a [] c) := by
   apply Relation.ReflTransGen.single
   simp [machine,cfg4,TM2.step,TM2.stepAux,store4,Function.update]
   funext k; cases k <;> rfl
 have h2 : TM2.Reaches machine
   (cfg4 .finishStream (some .frameEnd) (.frameEnd :: p) a [] c)
   (cfg4 .done none p a [] (.bit1 :: .tokenEnd :: c)) := by
   apply Relation.ReflTransGen.single
   simp [machine,cfg4,TM2.step,TM2.stepAux,store4,Function.update]
   funext k; cases k <;> rfl
 exact h0.trans (h1.trans h2)

theorem shifted_zero (f : ZFR.Formula) : shifted 0 f = ZFR.shift f := by
 have he : ZFR.sourceShiftIndex 0 = Nat.succ := by
   funext i
   simp [ZFR.sourceShiftIndex]
 simp only [shifted,he,ZFR.shift]

/-- Complete finite 4-stack formula shift, including frontend preparation and
return framing. All four surrounding stack tails are preserved exactly. -/
theorem shift_formula (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.prepare .formulaTag) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 .done none p a [] (TypedContext.value (.formula (ZFR.shift f)) ++ c)) := by
 have h0 := Routine.lift_embedded_run prepareRoles prepare_injective Q.prepare
   ReverseTokens.machine machine agree_prepare (fun _ => c)
   (ReverseTokens.reverse_formula f v a p) (by simp [config])
 simp only [embed_prepare] at h0
 have h1 : TM2.Reaches machine
   (cfg4 (.prepare .done) none (rev f ++ .frameEnd :: p) a [] c)
   (cfg4 .seed none (rev f ++ .frameEnd :: p) a [] c) := Relation.ReflTransGen.single rfl
 have h2 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
   (seed_step none (rev f ++ .frameEnd :: p) a c)
 have h3 := traverse f 0 none (.frameEnd :: p) (.frameEnd :: a) (.frameEnd :: c)
 have h4 := finish p a (forward (shifted 0 f) ++ .frameEnd :: c)
 have h := h0.trans (h1.trans (h2.trans (h3.trans h4)))
 simpa [TM2.Reaches,shifted_zero,TypedContext.value,valueSymbols,valueTokens,forward,payloadBits,List.flatMap_cons,tokenBits,Nat.one_bits,bitSymbol,List.append_assoc] using h

end RosserDirect.ShiftTraversal
