module
public import I3_334.Simulation.FrameExecution
public import I3_334.Machine.Startup
public import I3_334Support.Arithmetic.StandardReplay
@[expose] public section

namespace PalomarI3334.Stock

open PalomarI3380 PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell registers pack_registers)
open Engine (bits zeros)
open Control (root)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

def reserve : List Nat := List.replicate 132 0 ++ [1] ++ List.replicate 57 0

def bootFrame (path : List Bool) (gap : Nat) (working : List Nat) : Frame Nat :=
  ⟨path, gap, reserve ++ working⟩

def initialFrame : Frame Nat := bootFrame [] 18 (List.replicate 11 0)

def nextBootstrap (s : Frame Nat) : Option (Frame Nat) :=
  match executeWith s s.gap with
  | .next t => some t
  | _ => none

def advanceBootstrap : Nat → Frame Nat → Option (Frame Nat)
  | 0, s => some s
  | n+1, s => (nextBootstrap s).bind (advanceBootstrap n)

theorem advance_add (n k : Nat) (s : Frame Nat) :
    advanceBootstrap (n+k) s = (advanceBootstrap n s).bind (advanceBootstrap k) := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add, advanceBootstrap, Option.bind_some]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [advanceBootstrap]
    cases step : nextBootstrap s with
    | none => rfl
    | some t => exact ih t

private def boot28 : Frame Nat :=
  bootFrame (List.replicate 6 true ++ [false,true,true,false,false,false,true,true,true,false,false,true,false,true])
    17 [3,0,0,1,0,0,0,3,0,0,1]

private def boot56 : Frame Nat :=
  bootFrame (List.replicate 6 true ++ [false,true,true,false,false,false,true,true,true,false,true])
    33 [3,1,0,1,0,0,0,0,0,0,1]

private def boot84 : Frame Nat :=
  bootFrame (List.replicate 6 true ++ [false,true,true,false,false,true,true,true,true,true,false,true])
    48 [3,0,0,0,0,0,0,0,0,0,1]

def preparedFrame : Frame Nat :=
  bootFrame (List.replicate 6 true ++ [false,true,true,false,true,true,true,true,true,true,true,true,true,false,true])
    63 [2,0,0,0,0,0,0,0,0,0,1]

section BootstrapReplay
set_option maxRecDepth 16384
set_option maxHeartbeats 9000000

private theorem boot_first : advanceBootstrap 28 initialFrame = some boot28 := by decide +kernel
private theorem boot_second : advanceBootstrap 28 boot28 = some boot56 := by decide +kernel
private theorem boot_third : advanceBootstrap 28 boot56 = some boot84 := by decide +kernel
private theorem boot_fourth : advanceBootstrap 28 boot84 = some preparedFrame := by decide +kernel

end BootstrapReplay

theorem bootstrap_exact : advanceBootstrap 112 initialFrame = some preparedFrame := by
  change advanceBootstrap (28 + (28 + (28 + 28))) initialFrame = _
  rw [advance_add, boot_first, Option.bind_some, advance_add, boot_second, Option.bind_some,
    advance_add, boot_third, Option.bind_some]
  exact boot_fourth

private theorem standardSub : (Arithmetic.instSub_foundation : Sub Nat) = instSubNat := by
  change Sub.mk (Arithmetic.sub (V := Nat)) = Sub.mk Nat.sub
  apply congrArg Sub.mk
  funext a b
  symm
  apply Arithmetic.sub_eq_iff.mpr
  change (b = a ∨ b < a → a = b + (a-b)) ∧ (a < b → a-b = 0)
  omega

section ArithmeticInstances
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelCast : NatCast V := inferInstance
def modelZero : OfNat V 0 := inferInstance
def modelOne : OfNat V 1 := inferInstance
def modelAdd : Add V := inferInstance
noncomputable def modelSub : Sub V := inferInstance
noncomputable def modelDec : DecidableEq V := inferInstance

noncomputable def modelExecuteWith (s : Frame V) (pad : Nat) : Outcome V :=
  @executeWith V modelCast modelZero modelOne modelAdd modelSub modelDec s pad

end ArithmeticInstances

private theorem standardCast : (modelCast : NatCast Nat) = instNatCastNat := by
  change NatCast.mk (@Nat.cast Nat modelCast) = NatCast.mk (@Nat.cast Nat instNatCastNat)
  apply congrArg NatCast.mk
  funext n
  exact Arithmetic.natCast_nat n

theorem modelExecuteWith_nat (s : Frame Nat) (n : Nat) :
    modelExecuteWith s n = executeWith s n := by
  unfold modelExecuteWith
  have sub : (modelSub : Sub Nat) = instSubNat := standardSub
  have dec : (modelDec : DecidableEq Nat) = instDecidableEqNat := Subsingleton.elim _ _
  rw [standardCast, sub, dec]
  rfl

def Frame.config (s : Frame Nat) : Configuration :=
  ⟨root, 1, bits (s.path ++ (zeros s.gap ++ Engine.registers s.values))⟩

theorem Frame.code_nat (s : Frame Nat) : s.code = encodeLiteral s.config := by
  unfold Frame.code frame
  have reg : registers s.values (0 : Nat) = packWord (Engine.registers s.values) 0 :=
    (ArithmeticMachine.Reference.pack_registers_nil _ 0).symm
  rw [reg]
  have zerosEq := repeatBit_cast (M := Nat) false s.gap (packWord (Engine.registers s.values) 0)
  rw [Arithmetic.natCast_nat] at zerosEq
  rw [zerosEq, ← packWord_append, ← packWord_append, packWord_bits]
  simp only [Arithmetic.natCast_nat, Frame.config, cell, encodeLiteral, Engine.zeros, List.append_assoc]

end PalomarI3334.Stock
