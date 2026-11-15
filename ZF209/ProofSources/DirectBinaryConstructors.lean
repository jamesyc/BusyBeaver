module
public import DirectSegments
@[expose] public section
namespace RosserDirect.Binary
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Control where
 | boot | scanB | flushB | scanA | flushA | done | reject
 deriving DecidableEq, Fintype, Inhabited

/-- One concrete finite machine per binary constructor opcode. The boot phase
validates and removes B's Formula type tag; A's tag is retained in the result.
Both transfer phases run inside this single machine, not external callbacks. -/
def machine (opcode : Nat) : Control → Stmt Control
 | .boot => .pop .input (fun _ a => a)
   (.branch (fun a => a == some .bit1)
    (.pop .input (fun _ a => a)
     (.branch (fun a => a == some .tokenEnd)
      (.goto (fun _ => .scanB)) (.goto (fun _ => .reject))))
    (.goto (fun _ => .reject)))
 | .scanB => scanStmt .scanB .flushB .reject (tokenBits opcode ++ [.frameEnd])
 | .flushB => flushStmt .flushB .scanA
 | .scanA => scanStmt .scanA .flushA .reject []
 | .flushA => flushStmt .flushA .done
 | .done => .halt
 | .reject => .halt

theorem boot_step (opcode : Nat) (reg : Option Symbol) (a b c : List Symbol) :
 TM2.step (machine opcode) (config .boot reg (.bit1 :: .tokenEnd :: a) b c) =
 some (config .scanB (some .tokenEnd) a b c) := by
 simp [machine, config, TM2.step, TM2.stepAux, storage]
 funext k; cases k <;> rfl

theorem assemble (opcode : Nat) (pa pb : List Symbol)
    (ha : ∀ x ∈ pa, x ≠ .frameEnd) (hb : ∀ x ∈ pb, x ≠ .frameEnd)
    (reg : Option Symbol) (rest out : List Symbol) :
 TM2.Reaches (machine opcode)
  (config .boot reg (.bit1 :: .tokenEnd :: (pb ++ .frameEnd :: (pa ++ .frameEnd :: rest))) [] out)
  (config .done none rest [] (pa ++ pb ++ tokenBits opcode ++ .frameEnd :: out)) := by
 have h0 : TM2.Reaches (machine opcode)
  (config .boot reg (.bit1 :: .tokenEnd :: (pb ++ .frameEnd :: (pa ++ .frameEnd :: rest))) [] out)
  (config .scanB (some .tokenEnd) (pb ++ .frameEnd :: (pa ++ .frameEnd :: rest)) [] out) :=
   Relation.ReflTransGen.single (by rw [boot_step]; rfl)
 have h1 := transfer (machine opcode) .scanB .flushB .scanA .reject
   (tokenBits opcode ++ [.frameEnd]) rfl rfl pb hb (some .tokenEnd)
   (pa ++ .frameEnd :: rest) out
 have h2 := transfer (machine opcode) .scanA .flushA .done .reject [] rfl rfl
   pa ha none rest (pb ++ (tokenBits opcode ++ [.frameEnd]) ++ out)
 exact h0.trans (h1.trans (by simpa [TM2.Reaches, List.append_assoc] using h2))

@[simp] theorem formula_type_bits : tokenBits 1 = [.bit1, .tokenEnd] := by decide

end RosserDirect.Binary
