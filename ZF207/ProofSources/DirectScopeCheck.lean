module
public import ScopeFixedpoint
public import DirectFrameEquality
public import DirectFrameCopy
@[expose] public section
namespace RosserDirect.ScopeCheck
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

inductive Q where
 | copy (q : Label) | shift (q : DepthShift.Q)
 | compare (q : RosserDirectEquality.Label) | accept | reject
 deriving DecidableEq, Fintype, Inhabited

def compareRoles : Stack → K
 | .input => .stream | .scratch => .scratch | .output => .output

def machine : Q → Stmt4 Q
 | .copy .done => .goto (fun _ => .shift (.prepare .formulaTag))
 | .copy q => Routine.relocate prepareRoles Q.copy (Copy.machine q)
 | .shift .done => .goto (fun _ => .compare .scan)
 | .shift q => Routine.relocate id Q.shift (DepthShift.machine q)
 | .compare .equal => .goto (fun _ => .accept)
 | .compare .different => .goto (fun _ => .reject)
 | .compare q => Routine.relocate compareRoles Q.compare (RosserDirectEquality.machine q)
 | .accept | .reject => .halt

theorem agree_copy (q : Label) (h : Copy.machine q ≠ .halt) :
 machine (.copy q) = Routine.relocate prepareRoles Q.copy (Copy.machine q) := by
 cases q <;> simp_all [machine,Copy.machine]
theorem agree_shift (q : DepthShift.Q) (h : DepthShift.machine q ≠ .halt) :
 machine (.shift q) = Routine.relocate id Q.shift (DepthShift.machine q) := by
 cases q <;> simp_all [machine,DepthShift.machine]
theorem agree_compare (q : RosserDirectEquality.Label) (h : RosserDirectEquality.machine q ≠ .halt) :
 machine (.compare q) = Routine.relocate compareRoles Q.compare (RosserDirectEquality.machine q) := by
 cases q <;> simp_all [machine,RosserDirectEquality.machine]

def payload (f : ZFR.Formula) := payloadBits (1 :: ZFR.TokenVM.emitFormula f)
theorem value_formula (f : ZFR.Formula) :
 TypedContext.value (.formula f) = payload f ++ [.frameEnd] := rfl

theorem embed_copy (q : Label) (v : Option Symbol) (p a s c : List Symbol) :
 Routine.embed prepareRoles Q.copy (cfg q v a s p) (fun _ => c) =
 cfg4 (.copy q) v p a s c := by
 unfold Routine.embed cfg cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem prepare (f : ZFR.Formula) (n : Nat) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.copy .scan) v p (TypedContext.value (.formula f) ++ TypedContext.value (.nat n) ++ .frameEnd :: a) [] c)
  (cfg4 (.compare .scan) none (TypedContext.value (.formula f) ++ p) a []
   (TypedContext.value (.formula (DepthShift.shifted n f)) ++ c)) := by
 have h0 := Routine.lift_embedded_run prepareRoles prepare_injective Q.copy
   Copy.machine machine agree_copy (fun _ => c)
   (Copy.copy_frame (payload f) (payloadBits_no_end _) v
    (TypedContext.value (.nat n) ++ .frameEnd :: a) p) (by simp [cfg])
 simp only [embed_copy] at h0
 have h0' : TM2.Reaches machine
  (cfg4 (.copy .scan) v p (TypedContext.value (.formula f) ++ TypedContext.value (.nat n) ++ .frameEnd :: a) [] c)
  (cfg4 (.copy .done) none (TypedContext.value (.formula f) ++ p)
   (TypedContext.value (.formula f) ++ TypedContext.value (.nat n) ++ .frameEnd :: a) [] c) := by
  simpa only [value_formula,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using h0
 have h1 : TM2.Reaches machine
  (cfg4 (.copy .done) none (TypedContext.value (.formula f) ++ p)
   (TypedContext.value (.formula f) ++ TypedContext.value (.nat n) ++ .frameEnd :: a) [] c)
  (cfg4 (.shift (.prepare .formulaTag)) none (TypedContext.value (.formula f) ++ p)
   (TypedContext.value (.formula f) ++ TypedContext.value (.nat n) ++ .frameEnd :: a) [] c) :=
  Relation.ReflTransGen.single rfl
 have h2 := FourStack.relabel_run Q.shift DepthShift.machine machine agree_shift
   _ _ _ _ _ _ _ _ _ _ _ _ (DepthShift.shift_formula f n none (TypedContext.value (.formula f) ++ p) a c)
 have h3 : TM2.Reaches machine
  (cfg4 (.shift .done) none (TypedContext.value (.formula f) ++ p) a []
   (TypedContext.value (.formula (DepthShift.shifted n f)) ++ c)) _ := Relation.ReflTransGen.single rfl
 exact h0'.trans (h1.trans (h2.trans h3))

theorem compare_injective : Function.Injective compareRoles := by
 intro a b h; cases a <;> cases b <;> simp_all [compareRoles]

theorem embed_compare (q : RosserDirectEquality.Label) (v : Option Symbol) (p a s c : List Symbol) :
 Routine.embed compareRoles Q.compare (RosserDirectEquality.cfg q v p s c) (fun _ => a) =
 cfg4 (.compare q) v p a s c := by
 unfold Routine.embed RosserDirectEquality.cfg cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem accept (f : ZFR.Formula) (n : Nat) (hf : ZFR.Bound f n)
 (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.copy .scan) v p (TypedContext.value (.formula f) ++ TypedContext.value (.nat n) ++ .frameEnd :: a) [] c)
  (cfg4 .accept (some .frameEnd) p a [] c) := by
 have eqf := (ScopeFixedpoint.formula_fixed f n).mpr hf
 have h0 := prepare f n v p a c
 rw [eqf] at h0
 have h1 := Routine.lift_embedded_run compareRoles compare_injective Q.compare
   RosserDirectEquality.machine machine agree_compare (fun _ => a)
   (RosserDirectEquality.equal_frames (payload f) (payloadBits_no_end _) none p [] c)
   (by simp [RosserDirectEquality.cfg])
 simp only [embed_compare] at h1
 have h2 : TM2.Reaches machine
  (cfg4 (.compare .equal) (some .frameEnd) p a [] c)
  (cfg4 .accept (some .frameEnd) p a [] c) := Relation.ReflTransGen.single rfl
 apply h0.trans
 simpa only [value_formula,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using h1.trans h2

theorem reject (f : ZFR.Formula) (n : Nat) (hf : ¬ZFR.Bound f n)
 (v : Option Symbol) (p a c : List Symbol) :
 ∃ w p' c', TM2.Reaches machine
  (cfg4 (.copy .scan) v p (TypedContext.value (.formula f) ++ TypedContext.value (.nat n) ++ .frameEnd :: a) [] c)
  (cfg4 .reject w p' a [] c') := by
 have neq : payload f ≠ payload (DepthShift.shifted n f) := by
   intro h
   have he : f = DepthShift.shifted n f := by
    apply emitFormula_injective
    exact List.cons.inj (payloadBits_injective h) |>.2
   exact hf ((ScopeFixedpoint.formula_fixed f n).mp he.symm)
 obtain ⟨w,p',c',hr⟩ := RosserDirectEquality.unequal_frames
   (payload f) (payload (DepthShift.shifted n f)) (payloadBits_no_end _) (payloadBits_no_end _) neq none p [] c
 have h1 := Routine.lift_embedded_run compareRoles compare_injective Q.compare
   RosserDirectEquality.machine machine agree_compare (fun _ => a) hr (by simp [RosserDirectEquality.cfg])
 simp only [embed_compare] at h1
 have h2 : TM2.Reaches machine (cfg4 (.compare .different) w p' a [] c')
   (cfg4 .reject w p' a [] c') := Relation.ReflTransGen.single rfl
 refine ⟨w,p',c', (prepare f n v p a c).trans ?_⟩
 simpa only [value_formula,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using h1.trans h2

end RosserDirect.ScopeCheck
