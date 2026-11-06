import PA215PA.InternalUniformOracle
import PA215.Contract5114
namespace PA215.PA.InternalTrace.FileBoxes
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open PA215.Runtime Symbolic
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- The separate unchanged halt checker reaches actual dense halt code215
in every PA model. Unsupported rows are not interpreted as termination. -/
theorem checked_halt (n xs : V) (hsize : (10 : V)≤len xs) (fuel : Nat)
    (br : Branch) (initial : SConf) (hc : HaltContracts.check fuel br initial=true)
    (hg : Guard xs br) :
    ∃ k qs ls rs lf rf, 0<k ∧ Segment k qs ls rs
      (config n (box xs) denseControl initial).q
      (config n (box xs) denseControl initial).left
      (config n (box xs) denseControl initial).right 215 lf rf := by
  unfold HaltContracts.check at hc
  cases he : Runtime.exec NativeTable.machine br (fun s => s.1==254) fuel initial false with
  | none => simp [he] at hc
  | some last =>
    have ha := InternalOracleAlphabet.audit_covered br (fun s => s.1==254) fuel initial false
    have hs := audit_sound n (box xs) InternalOracleAlphabet.allowed br (fun s => s.1==254)
      (allowed_oracle n xs hsize br hg) (head xs) fuel initial false ha
    have h := exec_sound n (box xs) br (fun s => s.1==254) fuel initial false last he hs
    have hlast : last.1=254 := beq_iff_eq.mp h.1
    have hq : (config n (box xs) denseControl last).q=(215 : V) := by
      rcases last with ⟨q,onl,l,r⟩
      change q=254 at hlast
      subst q
      have hc : NativeRows.code 254=215 := by rfl
      cases onl <;> simp [config,denseControl,hc]
    obtain ⟨k,qs,ls,rs,hseg,hpos⟩ := h.2
    rw [hq] at hseg
    exact ⟨k,qs,ls,rs,_,_,hpos rfl,hseg⟩

/-- Exact terminal original5114 arithmetic simulation, kept separate from the
5,133 nonterminal contract family. -/
theorem terminal5114 (n xs : V) (hsize : (10 : V)≤len xs) :
    ∃ k qs ls rs lf rf, 0<k ∧ Segment k qs ls rs
      (config n (box xs) denseControl Contract5114.initial).q
      (config n (box xs) denseControl Contract5114.initial).left
      (config n (box xs) denseControl Contract5114.initial).right 215 lf rf :=
  checked_halt n xs hsize 4000 none Contract5114.initial Contract5114.checked trivial
end Models
#print axioms checked_halt
#print axioms terminal5114
end PA215.PA.InternalTrace.FileBoxes
