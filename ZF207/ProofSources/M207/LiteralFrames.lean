module
public import M207.Permutation
public import M207.FrameSoundness
@[expose] public section
namespace M207
open M6.Zip M6.Runtime

theorem literal_frame_certificate (br : Branch) (fuel : Nat) (start finish : SConf)
    (checked : (exec renamed br (fun s => sMatches s finish) fuel start false).isSome = true)
    (n : Nat) (vs : List Nat) (valid : Valid br vs) :
    Reach1 literal (mapConf forward (conc n vs start)) (mapConf forward (conc n vs finish)) :=
  literal_reach1 (certificate_to_frame br fuel start finish checked n vs valid)

private theorem conc_control (n : Nat) (vs : List Nat) (s : SConf) :
    (conc n vs s).q = s.1 := by
  obtain ⟨q,onl,l,r⟩ := s
  cases onl <;> rfl

theorem literal_terminal (c : Conf) (hq : c.q = 207) : step literal c = none := by
  obtain ⟨q,l,r⟩ := c
  simp only at hq
  subst q
  unfold step
  have ht : literal 207 (r.headD false) = none := by
    cases r.headD false <;> decide +kernel
  rw [ht]

theorem literal_halt_certificate (br : Branch) (fuel : Nat) (start : SConf)
    (checked : (exec renamed br (fun s => s.1 == inverse 207) fuel start false).isSome = true)
    (n : Nat) (vs : List Nat) (valid : Valid br vs) :
    Halts literal (mapConf forward (conc n vs start)) := by
  obtain ⟨finish, ht, hr⟩ := certificate_sound br _ fuel start checked n vs valid
  have hq : (mapConf forward (conc n vs finish)).q = 207 := by
    simp only [mapConf, conc_control]
    rw [beq_iff_eq.mp ht, forward_inverse]
  exact ⟨_, (literal_reach1 hr).reach, literal_terminal _ hq⟩
end M207
