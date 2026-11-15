module
public import ExecutableNDChecker
public import ExecutableZFProof
@[expose] public section
namespace ZFR.BottomUp
open Executable
set_option linter.unusedSimpArgs false

inductive Rule where
 | ctx (Γ : Context) (a : Formula)
 | pc (Γ : Context) (a b : Formula)
 | ii (Γ : Context) (a b : Formula)
 | ie (Γ : Context) (a b : Formula)
 | exp (Γ : Context) (a : Formula)
 | ci (Γ : Context) (a b : Formula)
 | ce1 (Γ : Context) (a b : Formula)
 | ce2 (Γ : Context) (a b : Formula)
 | di1 (Γ : Context) (a b : Formula)
 | di2 (Γ : Context) (a b : Formula)
 | branchPair (Γ : Context) (a b c : Formula)
 | de (Γ : Context) (a b c : Formula)
 | wk (Γ Δ : Context) (a : Formula)
 | allI (Γ : Context) (a : Formula)
 | allE (Γ : Context) (a : Formula) (t : Nat)
 | exI (Γ : Context) (a : Formula) (t : Nat)
 | exE (Γ : Context) (a c : Formula)
 deriving Repr


/-- Each instruction consumes already checked premise rows, never subtrees. -/
def step : Rule → List Checked → Option (List Checked)
 | .ctx Γ a, s =>
   let result : Option Checked :=
    if h : a ∈ Γ then some ⟨.seq Γ a, ND.ctx h⟩ else none
   result.map (fun r => r :: s)
 | .pc Γ a b, s =>
   let result : Option Checked :=
    some ⟨_, ND.pc Γ a b⟩
   result.map (fun r => r :: s)
 | .ii Γ a b, p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq (a :: Γ) b)
       pure ⟨_, ND.ii hp.down⟩
   result.map (fun r => r :: s)
 | .ie Γ a b, q :: p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq Γ (.imp a b))
       let hq ← demand (some q) (.seq Γ a)
       pure ⟨_, ND.ie hp.down hq.down⟩
   result.map (fun r => r :: s)
 | .exp Γ a, p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq Γ .bot)
       pure ⟨.seq Γ a, ND.exp hp.down⟩
   result.map (fun r => r :: s)
 | .ci Γ a b, q :: p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq Γ a)
       let hq ← demand (some q) (.seq Γ b)
       pure ⟨_, ND.ci hp.down hq.down⟩
   result.map (fun r => r :: s)
 | .ce1 Γ a b, p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq Γ (.and a b))
       pure ⟨_, ND.ce1 hp.down⟩
   result.map (fun r => r :: s)
 | .ce2 Γ a b, p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq Γ (.and a b))
       pure ⟨_, ND.ce2 hp.down⟩
   result.map (fun r => r :: s)
 | .di1 Γ a b, p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq Γ a)
       pure ⟨.seq Γ (.or a b), ND.di1 hp.down⟩
   result.map (fun r => r :: s)
 | .di2 Γ a b, p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq Γ b)
       pure ⟨.seq Γ (.or a b), ND.di2 hp.down⟩
   result.map (fun r => r :: s)
 | .branchPair Γ a b c, q :: p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq (a :: Γ) c)
       let hq ← demand (some q) (.seq (b :: Γ) c)
       pure ⟨_, ND.branchPair hp.down hq.down⟩
   result.map (fun r => r :: s)
 | .de Γ a b c, q :: p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq Γ (.or a b))
       let hq ← demand (some q) (.branches Γ a b c)
       pure ⟨_, ND.de hp.down hq.down⟩
   result.map (fun r => r :: s)
 | .wk Γ Δ a, p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq Γ a)
       if h : ∀ x ∈ Γ, x ∈ Δ then
         pure ⟨_, ND.wk h hp.down⟩
       else none
   result.map (fun r => r :: s)
 | .allI Γ a, p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq (shiftContext Γ) a)
       pure ⟨_, ND.allI hp.down⟩
   result.map (fun r => r :: s)
 | .allE Γ a t, p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq Γ (.all a))
       pure ⟨_, ND.allE t hp.down⟩
   result.map (fun r => r :: s)
 | .exI Γ a t, p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq Γ (subst t a))
       pure ⟨_, ND.exI t hp.down⟩
   result.map (fun r => r :: s)
 | .exE Γ a c, q :: p :: s =>
   let result : Option Checked :=
    do
       let hp ← demand (some p) (.seq Γ (.ex a))
       let hq ← demand (some q) (.seq (a :: shiftContext Γ) (shift c))
       pure ⟨_, ND.exE hp.down hq.down⟩
   result.map (fun r => r :: s)
 | _, _ => none

def run : List Rule → List Checked → Option (List Checked)
 | [], s => some s
 | r :: rs, s => step r s >>= run rs

theorem run_append (a b : List Rule) (s : List Checked) :
 run (a ++ b) s = run a s >>= run b := by
 induction a generalizing s with
 | nil => rfl
 | cons r rs ih =>
   simp only [List.cons_append, run]
   cases step r s with
   | none => rfl
   | some t => exact ih t

def emit : Cert → List Rule
 | .ctx Γ a => [.ctx Γ a]
 | .pc Γ a b => [.pc Γ a b]
 | .ii Γ a b p => emit p ++ [.ii Γ a b]
 | .ie Γ a b p q => emit p ++ emit q ++ [.ie Γ a b]
 | .exp Γ a p => emit p ++ [.exp Γ a]
 | .ci Γ a b p q => emit p ++ emit q ++ [.ci Γ a b]
 | .ce1 Γ a b p => emit p ++ [.ce1 Γ a b]
 | .ce2 Γ a b p => emit p ++ [.ce2 Γ a b]
 | .di1 Γ a b p => emit p ++ [.di1 Γ a b]
 | .di2 Γ a b p => emit p ++ [.di2 Γ a b]
 | .branchPair Γ a b c p q => emit p ++ emit q ++ [.branchPair Γ a b c]
 | .de Γ a b c p q => emit p ++ emit q ++ [.de Γ a b c]
 | .wk Γ Δ a p => emit p ++ [.wk Γ Δ a]
 | .allI Γ a p => emit p ++ [.allI Γ a]
 | .allE Γ a t p => emit p ++ [.allE Γ a t]
 | .exI Γ a t p => emit p ++ [.exI Γ a t]
 | .exE Γ a c p q => emit p ++ emit q ++ [.exE Γ a c]

/-- Exact equivalence, including rejection, for any existing stack suffix. -/
theorem run_emit (c : Cert) (s : List Checked) :
 run (emit c) s = (Executable.check c).map (fun r => r :: s) := by
 induction c generalizing s with
 | ctx Γ a =>
   simp [emit, run, step, Executable.check]
 | pc Γ a b =>
   simp [emit, run, step, Executable.check]
 | ii Γ a b p ip =>
   simp only [emit, run_append, ip]
   cases hp : Executable.check p <;>
    simp [Executable.check, run, step, demand, hp, ip]
 | ie Γ a b p q ip iq =>
   simp only [emit, run_append, ip, iq]
   cases hp : Executable.check p <;>
   cases hq : Executable.check q <;>
    simp [Executable.check, run, step, demand, hp, hq, ip, iq]
 | exp Γ a p ip =>
   simp only [emit, run_append, ip]
   cases hp : Executable.check p <;>
    simp [Executable.check, run, step, demand, hp, ip]
 | ci Γ a b p q ip iq =>
   simp only [emit, run_append, ip, iq]
   cases hp : Executable.check p <;>
   cases hq : Executable.check q <;>
    simp [Executable.check, run, step, demand, hp, hq, ip, iq]
 | ce1 Γ a b p ip =>
   simp only [emit, run_append, ip]
   cases hp : Executable.check p <;>
    simp [Executable.check, run, step, demand, hp, ip]
 | ce2 Γ a b p ip =>
   simp only [emit, run_append, ip]
   cases hp : Executable.check p <;>
    simp [Executable.check, run, step, demand, hp, ip]
 | di1 Γ a b p ip =>
   simp only [emit, run_append, ip]
   cases hp : Executable.check p <;>
    simp [Executable.check, run, step, demand, hp, ip]
 | di2 Γ a b p ip =>
   simp only [emit, run_append, ip]
   cases hp : Executable.check p <;>
    simp [Executable.check, run, step, demand, hp, ip]
 | branchPair Γ a b c p q ip iq =>
   simp only [emit, run_append, ip, iq]
   cases hp : Executable.check p <;>
   cases hq : Executable.check q <;>
    simp [Executable.check, run, step, demand, hp, hq, ip, iq]
 | de Γ a b c p q ip iq =>
   simp only [emit, run_append, ip, iq]
   cases hp : Executable.check p <;>
   cases hq : Executable.check q <;>
    simp [Executable.check, run, step, demand, hp, hq, ip, iq]
 | wk Γ Δ a p ip =>
   simp only [emit, run_append, ip]
   cases hp : Executable.check p <;>
    simp [Executable.check, run, step, demand, hp, ip]
 | allI Γ a p ip =>
   simp only [emit, run_append, ip]
   cases hp : Executable.check p <;>
    simp [Executable.check, run, step, demand, hp, ip]
 | allE Γ a t p ip =>
   simp only [emit, run_append, ip]
   cases hp : Executable.check p <;>
    simp [Executable.check, run, step, demand, hp, ip]
 | exI Γ a t p ip =>
   simp only [emit, run_append, ip]
   cases hp : Executable.check p <;>
    simp [Executable.check, run, step, demand, hp, ip]
 | exE Γ a c p q ip iq =>
   simp only [emit, run_append, ip, iq]
   cases hp : Executable.check p <;>
   cases hq : Executable.check q <;>
    simp [Executable.check, run, step, demand, hp, hq, ip, iq]

def evaluate (program : List Rule) : Option Checked := do
 match ← run program [] with
 | [r] => some r
 | _ => none

@[simp] theorem evaluate_emit (c : Cert) : evaluate (emit c) = Executable.check c := by
 unfold evaluate
 rw [run_emit]
 cases Executable.check c <;> rfl

def conclusion (program : List Rule) : Option Row := (evaluate program).map Subtype.val

theorem sound (program : List Rule) (r : Row) (h : conclusion program = some r) : ND r := by
 unfold conclusion at h
 cases he : evaluate program with
 | none => simp [he] at h
 | some checked =>
   have hr : checked.val = r := by simpa [he] using h
   exact hr ▸ checked.property

theorem complete {r : Row} (h : ND r) : ∃ program, conclusion program = some r := by
 obtain ⟨c, hc⟩ := Executable.complete_checked h
 exact ⟨emit c, by simp [conclusion, hc]⟩

end ZFR.BottomUp
