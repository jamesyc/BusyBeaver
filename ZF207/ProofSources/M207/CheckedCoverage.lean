module
public import M207.SourceData


@[expose] public section

namespace M207.Source.CheckedCoverage

open M207.Source M6.Runtime

def frameCheck (pc : Nat) (branch : Branch) (fuel : Nat) (finish : SConf) : Bool :=
  (exec M207.renamed branch (fun s => sMatches s finish) fuel (rootFrame (paths pc)) false).isSome

def instructionCheck (pc : Nat) (fuel : Nat) : Instruction → Bool
  | .inc r k =>
    decide ((paths k).length ≤ 48) && frameCheck pc none fuel (rootFrame (paths k) 0 (.inc r))
  | .dec r z p =>
    decide ((paths z).length ≤ 48) && (decide ((paths p).length ≤ 48) &&
      (frameCheck pc (some (r, true)) fuel (rootFrame (paths z)) &&
        frameCheck pc (some (r, false)) fuel (rootFrame (paths p) 1 (.dec r))))
  | .jump k =>
    decide ((paths k).length ≤ 48) && frameCheck pc none fuel (rootFrame (paths k))
  | .halt =>
    (exec M207.renamed none (fun s => s.1 == M207.inverse 207)
      fuel (rootFrame (paths pc)) false).isSome

def siteCheck (pc fuel : Nat) : Bool :=
  match program pc with
  | none => false
  | some code =>
    decide (instructionBound 4341 code) &&
      (decide ((paths pc).length ≤ 48) && instructionCheck pc fuel code)

theorem siteCheck_sound {pc fuel : Nat} {code : Instruction}
    (instruction : program pc = some code) (checked : siteCheck pc fuel = true) :
    instructionBound 4341 code ∧ (paths pc).length ≤ 48 ∧ instructionCheck pc fuel code = true := by
  simpa only [siteCheck, instruction, Bool.and_eq_true, decide_eq_true_eq] using checked

def blockCheck (fuel : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | base, count + 1 => siteCheck base fuel && blockCheck fuel (base + 1) count

theorem append_checks {fuel base left right : Nat}
    (first : blockCheck fuel base left = true)
    (second : blockCheck fuel (base + left) right = true) :
    blockCheck fuel base (left + right) = true := by
  induction left generalizing base with
  | zero => simpa only [Nat.add_zero, Nat.zero_add] using second
  | succ left ih =>
    have checks : siteCheck base fuel = true ∧ blockCheck fuel (base + 1) left = true := by
      simpa only [blockCheck, Bool.and_eq_true] using first
    have eq : base + 1 + left = base + left.succ := by omega
    rw [← eq] at second
    have rest := ih checks.2 second
    simpa only [Nat.succ_add, blockCheck, Bool.and_eq_true] using And.intro checks.1 rest

theorem of_blockCheck {P : Nat → Prop}
    (sound : ∀ pc fuel, siteCheck pc fuel = true → P pc) (fuel base count : Nat)
    (checked : blockCheck fuel base count = true) :
    ∀ i, i < count → P (base + i) := by
  induction count generalizing base with
  | zero => simp
  | succ count ih =>
    have checks : siteCheck base fuel = true ∧ blockCheck fuel (base + 1) count = true := by
      simpa only [blockCheck, Bool.and_eq_true] using checked
    intro i hi
    cases i with
    | zero => exact sound base fuel checks.1
    | succ i =>
      have eq : base + 1 + i = base + (i + 1) := by omega
      rw [← eq]
      exact ih (base + 1) checks.2 i (by simpa using hi)

/-- A bound for the symbolic executor at every source site and on both branches. -/
def fuelLimit : Nat := 534

end M207.Source.CheckedCoverage
