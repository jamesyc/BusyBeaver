module
public import DirectTM2Frames
public import TokenCertificateVM
public import Mathlib.Data.Nat.Bits
@[expose] public section
namespace RosserDirect
open Turing

def bitSymbol : Bool → Symbol
 | false => .bit0
 | true => .bit1

def tokenBits (n : Nat) : List Symbol := n.bits.map bitSymbol ++ [.tokenEnd]
def payloadBits (tokens : List Nat) : List Symbol := tokens.flatMap tokenBits

theorem bitSymbol_ne_end (b : Bool) : bitSymbol b ≠ .frameEnd := by cases b <;> decide

theorem tokenBits_no_end (n : Nat) : ∀ x ∈ tokenBits n, x ≠ .frameEnd := by
 intro x hx
 simp only [tokenBits, List.mem_append, List.mem_map, List.mem_singleton] at hx
 rcases hx with ⟨b, hb, rfl⟩ | rfl
 · exact bitSymbol_ne_end b
 · decide

theorem payloadBits_no_end (ts : List Nat) : ∀ x ∈ payloadBits ts, x ≠ .frameEnd := by
 intro x hx
 obtain ⟨n, hn, hx⟩ := List.mem_flatMap.mp hx
 exact tokenBits_no_end n x hx

/-- Type tags and existing VM token syntax; each natural token is represented
by bits plus a token separator. A separate frame delimiter cannot occur inside. -/
def valueTokens : ZFR.TokenVM.Value → List Nat
 | .nat n => [0,n]
 | .formula a => 1 :: ZFR.TokenVM.emitFormula a
 | .context c => 2 :: ZFR.TokenVM.emitContext c
 | .cert c => 3 :: ZFR.TokenVM.emitCert c
 | .witness w => 4 :: ZFR.TokenVM.emitWitness w
 | .witnesses ws => 5 :: ZFR.TokenVM.emitWitnesses ws

def valueSymbols (v : ZFR.TokenVM.Value) : List Symbol :=
 payloadBits (valueTokens v) ++ [.frameEnd]

end RosserDirect
