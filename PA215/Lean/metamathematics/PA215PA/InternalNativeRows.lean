import PA215PA.InternalLeftPhase
import PA215PA.InternalScanRight
import PA215PA.ZipNatTape
namespace PA215.PA.InternalTrace.NativeRows
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open NativeTable ScanBits
attribute [local irreducible] Step StepFormula.formula

def code (q : Nat) : Nat := StepFormula.controlCode (inverse q)

/-- Exact sparse-label to dense-row binding, including the unique halt code. -/
theorem row_of_native {q q' : Nat} {b w dir : Bool}
    (h : machine q b=some (w,dir,q')) :
    ∃ d : WorkingState, inverse q=some d ∧ row d b=⟨w,dir,inverse q'⟩ := by
  cases hi : inverse q with
  | none => simp [machine,hi] at h
  | some d =>
    refine ⟨d,rfl,?_⟩
    cases ha : row d b with
    | mk aw ar an =>
      simp only [machine,hi,Option.map_some,Option.some.injEq,ha,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,hq⟩
      have hn := congrArg inverse hq
      simp only [ZipNatTape.inverse_labelControl] at hn
      rw [← hn]

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
theorem right {q q' : Nat} {b w : Bool} (h : machine q b=some (w,true,q')) (l t : V) :
    Step (code q : V) l ((1+1)*t+b.toNat) (code q' : V) ((1+1)*l+w.toNat) t := by
  obtain ⟨d,hi,hr⟩ := row_of_native h
  have hs := right_row d b (by rw [hr]) l t
  rw [hr] at hs
  simpa only [code,hi,StepFormula.controlCode] using hs

theorem left {q q' : Nat} {b w : Bool} (h : machine q b=some (w,false,q')) (l t : V) :
    Step (code q : V) l ((1+1)*t+b.toNat) (code q' : V)
      (l/2) ((1+1)*((1+1)*t+w.toNat)+l%2) := by
  obtain ⟨d,hi,hr⟩ := row_of_native h
  have hs := LeftPhase.left_row_any d b (by rw [hr]) l t
  rw [hr] at hs
  simpa only [code,hi,StepFormula.controlCode] using hs

theorem scan_right {q : Nat} {b w : Bool} (h : machine q b=some (w,true,q)) (n l t : V) :
    ∃ qs ls rs, Segment n qs ls rs (code q) l (repeatBits n b.toNat t)
      (code q) (repeatBits n w.toNat l) t := by
  obtain ⟨d,hi,hr⟩ := row_of_native h
  rw [hi] at hr
  have hs := ScanRight.segment d b w hr n l t
  simpa only [code,hi,StepFormula.controlCode] using hs

theorem scan_left {q : Nat} {b w : Bool} (h : machine q b=some (w,false,q)) (n l t : V) :
    ∃ qs ls rs, Phase n qs ls rs (code q) (repeatBits n b.toNat l) t
      (code q) l (repeatBits n w.toNat t) := by
  obtain ⟨d,hi,hr⟩ := row_of_native h
  rw [hi] at hr
  have hs := LeftPhase.segment d b w hr n l t
  simpa only [Phase,code,hi,StepFormula.controlCode] using hs
end Models
#print axioms row_of_native
#print axioms right
#print axioms left
#print axioms scan_right
#print axioms scan_left
end PA215.PA.InternalTrace.NativeRows
