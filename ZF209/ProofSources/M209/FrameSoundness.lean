module
public import M209.Literal
@[expose] public section
namespace M209
open M6.Zip M6.Runtime

/-- A successful *kernel-evaluated* runtime certificate produces positive literal
execution in the renamed machine, for every gap and valid complete register file.
No claim about the 5,644 certificates is assumed here. -/
theorem certificate_sound (br : Branch) (target : SConf → Bool)
    (fuel : Nat) (start : SConf)
    (checked : (exec renamed br target fuel start false).isSome = true)
    (n : Nat) (vs : List Nat) (valid : Valid br vs) :
    ∃ finish, target finish = true ∧
      Reach1 renamed (conc n vs start) (conc n vs finish) := by
  generalize he : exec renamed br target fuel start false = answer at checked
  cases answer with
  | none => simp at checked
  | some finish =>
    obtain ⟨ht, _, hp⟩ := exec_sound native_boxes n valid fuel start false finish he
    exact ⟨finish, ht, hp rfl⟩

/-- Matching compares the complete symbolic file, not merely a register prefix. -/
theorem certificate_to_frame (br : Branch) (fuel : Nat) (start finish : SConf)
    (checked : (exec renamed br (fun s => sMatches s finish) fuel start false).isSome = true)
    (n : Nat) (vs : List Nat) (valid : Valid br vs) :
    Reach1 renamed (conc n vs start) (conc n vs finish) := by
  obtain ⟨actual, hm, hr⟩ := certificate_sound br _ fuel start checked n vs valid
  rw [sMatches_conc n vs hm] at hr
  exact hr
end M209
