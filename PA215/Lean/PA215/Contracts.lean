import PA215.NativeTable

namespace PA215.Contracts
open PA215.Zip PA215.Runtime PA215.NativeTable

/-- A nonhalting original symbolic primitive obligation. Branch assumptions and
    entire initial/target frames are part of the data, not checker options. -/
structure Contract where
  branch : Branch
  initial : SConf
  target : SConf
  deriving Repr

def check (fuel : Nat) (c : Contract) : Bool :=
  (exec machine c.branch (fun s => sMatches s c.target) fuel c.initial false).isSome

/-- A successful closed certificate check yields its original full-frame theorem. -/
theorem sound (fuel : Nat) (c : Contract) (hc : check fuel c = true)
    (n : Nat) (vs : List Nat) (hv : Valid c.branch vs) :
    Reach1 machine (conc n vs c.initial) (conc n vs c.target) := by
  unfold check at hc
  cases he : exec machine c.branch (fun s => sMatches s c.target) fuel c.initial false with
  | none => simp [he] at hc
  | some last =>
      have h := exec_sound native_boxes n hv fuel c.initial false last he
      have hm := sMatches_conc n vs h.1
      simpa only [hm] using h.2.2 rfl

end PA215.Contracts
