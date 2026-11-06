import PA215.Source.PrimitiveSimulation
import PA215.ContractPilot
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.Source
open PA215.Runtime PA215.Zip

private def originalZero := PA215.Census.C000.records[0]'(by decide)
private def originalPositive := PA215.Census.C000.records[1]'(by decide)

/-- The first literal source instruction (Dec L), zero branch: actual dense
machine strict reach and exact source transition agree for EVERY full file. -/
theorem first_zero_simulation (n : Nat) (vs : List Nat)
    (hlen : 10 ≤ vs.length) (hz : vs.getD 1 0 = 0) :
    cycleStep exactSites ⟨.at 0,readFile vs⟩ = ⟨.at 2,readFile vs⟩ ∧
    Reach1 PA215.NativeTable.machine
      (conc n vs (rootFrame [false,false,false,false]))
      (conc n vs (rootFrame [false,false,true,false,false])) := by
  have hd := List.all_eq_true.mp original_first128_destinations originalZero (by decide)
  have h := checked_primitive_simulation
    (r := originalZero) (s := ⟨[false,false,false,false],.dec 8⟩)
    (i := .dec 8 (some 2) (some 1))
    (p := ⟨[false,false,true],0,.none⟩) (q := .at 2) (e := .none) (k := 2)
    (next := ⟨[false,false,true,false,false],.dec 0⟩)
    (t := PA215.ContractPilot.c0.target) (fuel := 4000)
    (by decide) (by decide) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide) hd PA215.ContractPilot.checked0 n vs ⟨hlen,hz⟩
  simpa only [effectFile, Nat.add_zero, show originalZero.siteIndex = 0 from rfl] using h

/-- Positive branch includes the one-cell padding shift and full file decrement;
its spare tail is retained rather than removed at the source/physical boundary. -/
theorem first_positive_simulation (n : Nat) (vs : List Nat)
    (hlen : 10 ≤ vs.length) (hz : vs.getD 1 0 ≠ 0) :
    cycleStep exactSites ⟨.at 0,readFile vs⟩ =
      ⟨.at 1,readFile (Runtime.decr 1 vs)⟩ ∧
    Reach1 PA215.NativeTable.machine
      (conc n vs (rootFrame [false,false,false,false]))
      (conc (n+1) (Runtime.decr 1 vs) (rootFrame [false,false,false,true])) := by
  have hd := List.all_eq_true.mp original_first128_destinations originalPositive (by decide)
  have h := checked_primitive_simulation
    (r := originalPositive) (s := ⟨[false,false,false,false],.dec 8⟩)
    (i := .dec 8 (some 2) (some 1))
    (p := ⟨[false,false,false,true],1,.dec 1⟩) (q := .at 1) (e := .dec 1) (k := 1)
    (next := ⟨[false,false,false,true],.breakTo 1⟩)
    (t := PA215.ContractPilot.c1.target) (fuel := 4000)
    (by decide) (by decide) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide) hd PA215.ContractPilot.checked1 n vs ⟨hlen,hz⟩
  exact h

#print axioms first_zero_simulation
#print axioms first_positive_simulation
end PA215.Source
