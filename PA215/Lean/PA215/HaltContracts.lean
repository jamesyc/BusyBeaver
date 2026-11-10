import PA215.Contracts

namespace PA215.HaltContracts
open PA215.Zip PA215.Runtime PA215.NativeTable

def check (fuel : Nat) (br : Branch) (initial : SConf) : Bool :=
  (exec machine br (fun s => s.1 == 254) fuel initial false).isSome

theorem terminal_row (b : Bool) : machine 254 b = none := by
  have hi : inverse 254 = none := by decide
  simp [machine, hi]

theorem conc_control (n : Nat) (vs : List Nat) (s : SConf) : (conc n vs s).q = s.1 := by
  rcases s with ⟨q, onLeft, l, r⟩
  cases onLeft <;> rfl

/-- Acceptance reaches the actual terminal control254, never an unsupported rule. -/
theorem positive_sound (fuel : Nat) (br : Branch) (initial : SConf)
    (hc : check fuel br initial = true) (n : Nat) (vs : List Nat) (hv : Valid br vs) :
    ∃ final, Reach1 machine (conc n vs initial) final ∧ final.q = 254 := by
  unfold check at hc
  cases he : exec machine br (fun s => s.1 == 254) fuel initial false with
  | none => simp [he] at hc
  | some last =>
      have h := exec_sound native_boxes n hv fuel initial false last he
      refine ⟨conc n vs last, h.2.2 rfl, ?_⟩
      rw [conc_control]
      exact beq_iff_eq.mp h.1

theorem sound (fuel : Nat) (br : Branch) (initial : SConf)
    (hc : check fuel br initial = true) (n : Nat) (vs : List Nat) (hv : Valid br vs) :
    PA215.Zip.Halts machine (conc n vs initial) := by
  obtain ⟨final, hreach, hq⟩ := positive_sound fuel br initial hc n vs hv
  refine ⟨final, hreach.reach, ?_⟩
  simp [PA215.Zip.step, hq, terminal_row]

end PA215.HaltContracts
