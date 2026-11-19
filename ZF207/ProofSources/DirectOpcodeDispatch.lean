module
public import DirectFramedRowConstructors
public import Mathlib.Data.Fintype.Sigma
@[expose] public section
namespace RosserDirect.OpcodeDispatch
open Turing Segment
set_option backward.isDefEq.respectTransparency false

/-- All counters are bounded finite control, not unbounded machine registers.
Natural-data tokens are routed before reading their arbitrarily long payload. -/
inductive Control where
 | start | scan (position : Fin 7) (value : Fin 64)
 | opcode (number : Fin 42) | natPayload | natZero | reject
 deriving DecidableEq, Fintype, Inhabited

def active : Control → Prop
 | .start | .scan _ _ => True
 | _ => False
instance (q : Control) : Decidable (active q) := by cases q <;> unfold active <;> infer_instance

def bitAdvance (k : Fin 7) (n : Fin 64) (bit : Bool) : Control :=
 let m := n.val + if bit then 2^k.val else 0
 if hk : k.val < 6 then
   if hm : m < 64 then .scan ⟨k.val+1,by omega⟩ ⟨m,hm⟩ else .reject
 else .reject

def advance : Control → Symbol → Control
 | .start, .bit1 => .scan 0 0
 | .start, .bit0 => .natPayload
 | .start, .tokenEnd => .natZero
 | .start, .frameEnd => .reject
 | .scan k n, .bit0 => bitAdvance k n false
 | .scan k n, .bit1 => bitAdvance k n true
 | .scan _ n, .tokenEnd => if h : n.val < 42 then .opcode ⟨n.val,h⟩ else .reject
 | .scan _ _, .frameEnd => .reject
 | q, _ => q

def machine (q : Control) : Stmt Control :=
 if active q then .pop .input (fun _ x => x)
   (.branch Option.isSome (.goto (fun x => advance q (x.getD .bit0)))
    (.goto (fun _ => .reject)))
 else .halt

def pathCheck : Control → List Symbol → Control → Bool
 | q, [], r => decide (q = r)
 | q, x :: xs, r => decide (active q) && pathCheck (advance q x) xs r

theorem symbol_step (q : Control) (ha : active q) (x : Symbol)
    (v : Option Symbol) (a scratch out : List Symbol) :
 TM2.step machine (config q v (x :: a) scratch out) =
 some (config (advance q x) (some x) a scratch out) := by
 cases x <;> simp [machine, ha, config, TM2.step, TM2.stepAux, storage, Function.update]
 all_goals funext k; cases k <;> rfl

theorem path_sound (q r : Control) (p : List Symbol) (h : pathCheck q p r = true)
    (v : Option Symbol) (a scratch out : List Symbol) :
 ∃ w, TM2.Reaches machine (config q v (p ++ a) scratch out)
   (config r w a scratch out) := by
 induction p generalizing q v with
 | nil =>
   have he : q = r := of_decide_eq_true h
   subst q
   exact ⟨v,Relation.ReflTransGen.refl⟩
 | cons x xs ih =>
   have hh : active q ∧ pathCheck (advance q x) xs r = true := by simpa [pathCheck] using h
   have ha := hh.1
   obtain ⟨w,hw⟩ := ih (advance q x) hh.2 (some x)
   have one : TM2.Reaches machine (config q v ((x :: xs) ++ a) scratch out)
     (config (advance q x) (some x) (xs ++ a) scratch out) :=
     Relation.ReflTransGen.single (by rw [List.cons_append,symbol_step q ha]; rfl)
   exact ⟨w,one.trans hw⟩

/-- Small finite control certificate: 42 opcode encodings, at most seven bits
apiece. Ordinary kernel decision, not native_decide or a large syntax numeral. -/
theorem all_opcodes : ∀ op : Fin 42,
 pathCheck .start (tokenBits (2*op.val+1)) (.opcode op) = true := by
 decide

/-- Concrete dispatch of every existing token VM constructor opcode. This
selects the correct finite entry; the opcode-specific body is linked separately. -/
theorem dispatch_opcode (op : Fin 42) (v : Option Symbol) (rest scratch out : List Symbol) :
 ∃ w, TM2.Reaches machine
   (config .start v (tokenBits (2*op.val+1) ++ rest) scratch out)
   (config (.opcode op) w rest scratch out) :=
 path_sound .start (.opcode op) _ (all_opcodes op) v rest scratch out

theorem dispatch_nat_zero (v : Option Symbol) (rest scratch out : List Symbol) :
 TM2.step machine (config .start v (tokenBits 0 ++ rest) scratch out) =
 some (config .natZero (some .tokenEnd) rest scratch out) := by
 simpa [tokenBits,advance] using symbol_step .start trivial .tokenEnd v rest scratch out

theorem dispatch_nat_positive (n : Nat) (hn : n ≠ 0)
    (v : Option Symbol) (rest scratch out : List Symbol) :
 TM2.step machine (config .start v (tokenBits (2*n) ++ rest) scratch out) =
 some (config .natPayload (some .bit0) (tokenBits n ++ rest) scratch out) := by
 have hb : (2*n).bits = false :: n.bits := Nat.bit0_bits n hn
 simpa [tokenBits,hb,bitSymbol,List.append_assoc,advance] using
   symbol_step .start trivial .bit0 v (tokenBits n ++ rest) scratch out

end RosserDirect.OpcodeDispatch
