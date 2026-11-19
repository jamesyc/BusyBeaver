module
public import M207.Conjugacy
@[expose] public section
namespace M207
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem forward_inverse_finite : ∀ q : Fin 210, forward (inverse q.val) = q.val := by decide
theorem forward_inverse (q : Nat) : forward (inverse q) = q := by
  by_cases h : q < 210
  · exact forward_inverse_finite ⟨q,h⟩
  · simp [forward, inverse, h]

/-- Once checked, this transports native/runtime positive steps to literal207. -/
theorem literal_reach1 {a b : Conf} (h : Reach1 renamed a b) :
    Reach1 literal (mapConf forward a) (mapConf forward b) :=
  renamed_reach1 forward_inverse h
end M207
