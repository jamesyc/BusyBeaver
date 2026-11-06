import PA215.Source.AXCode
import PA215PA.NativeCalculus

/-! Definitional bridge between core pure PA135 output arithmetic and the
one existing native proof calculus. No source execution is assumed here. -/
namespace PA215.PA.NativeCalculus

theorem core_heads_eq (a b c u h : Nat) :
    PA215.Source.AXCode.pa135Heads a b c u h = pa135Heads a b c u h := by
  simp only [PA215.Source.AXCode.pa135Heads, PA215.Source.AXCode.rho1, PA215.Source.AXCode.rho2, PA215.Source.AXCode.rho3, PA215.Source.AXCode.rho4, PA215.Source.AXCode.rho5, PA215.Source.AXCode.rho6, PA215.Source.AXCode.rho7, PA215.Source.AXCode.rho8, PA215.Source.AXCode.wex, PA215.Source.AXCode.wn, PA215.Source.AXCode.wel, PA215.Source.AXCode.weq, PA215.Source.AXCode.wim, PA215.Source.AXCode.wal,
    pa135Heads, rho1, rho2, rho3, rho4, rho5, rho6, rho7, rho8, wex, wn, wel, weq, wim, wal]

theorem core_gate_eq (a b c : Nat) :
    PA215.Source.AXCode.gate a b c = gate a b c := by
  simp only [PA215.Source.AXCode.gate, PA215.Source.AXCode.bundle, PA215.Source.AXCode.wa, PA215.Source.AXCode.wex, PA215.Source.AXCode.wn, PA215.Source.AXCode.wel, PA215.Source.AXCode.weq, PA215.Source.AXCode.wim, PA215.Source.AXCode.wal,
    gate, bundle, wa, wex, wn, wel, weq, wim, wal]

theorem core_bundle_eq (a b c : Nat) :
    PA215.Source.AXCode.bundle a b c = bundle a b c := by
  simp only [PA215.Source.AXCode.bundle, PA215.Source.AXCode.wa, PA215.Source.AXCode.wex, PA215.Source.AXCode.wn, PA215.Source.AXCode.wel, PA215.Source.AXCode.weq, PA215.Source.AXCode.wim, PA215.Source.AXCode.wal,
    bundle, wa, wex, wn, wel, weq, wim, wal]

theorem core_heads_proved (a b c u h : Nat) (hdom : u ≤ a) (hh : Proved h) :
    ∀ n ∈ PA215.Source.AXCode.pa135Heads a b c u h, Proved n := by
  rw [core_heads_eq]
  exact pa135Heads_proved a b c u h hdom hh

theorem core_gate_proved (a b c : Nat) : Proved (PA215.Source.AXCode.gate a b c) := by
  rw [core_gate_eq]
  exact gate_proved a b c

#print axioms core_heads_eq
#print axioms core_heads_proved
#print axioms core_gate_proved
end PA215.PA.NativeCalculus
