module
public import ExecutableZFProof
@[expose] public section
namespace ZFR.TokenVM

/-- Runtime values of the decoding VM. No proof fields or numeric pairing. -/
inductive Value where
 | nat : Nat → Value
 | formula : Formula → Value
 | context : Context → Value
 | cert : Executable.Cert → Value
 | witness : ExecutableZF.AxiomWitness → Value
 | witnesses : List ExecutableZF.AxiomWitness → Value
 deriving Repr

/-- Even tokens carry natural-number data; odd tokens are constructor opcodes.
Variables are individual payloads, never enormous encodings of syntax trees. -/
def instruction : Nat → List Value → Option (List Value)
 | 0, s => some (.formula (.bot ) :: s)
 | 1, .nat a1 :: .nat a0 :: s => some (.formula (.mem a0 a1) :: s)
 | 2, .nat a1 :: .nat a0 :: s => some (.formula (.eq a0 a1) :: s)
 | 3, .formula a1 :: .formula a0 :: s => some (.formula (.and a0 a1) :: s)
 | 4, .formula a1 :: .formula a0 :: s => some (.formula (.or a0 a1) :: s)
 | 5, .formula a1 :: .formula a0 :: s => some (.formula (.imp a0 a1) :: s)
 | 6, .formula a0 :: s => some (.formula (.all a0) :: s)
 | 7, .formula a0 :: s => some (.formula (.ex a0) :: s)
 | 8, s => some (.context [] :: s)
 | 9, .context tail :: .formula head :: s => some (.context (head :: tail) :: s)
 | 10, .formula a1 :: .context a0 :: s => some (.cert (.ctx a0 a1) :: s)
 | 11, .formula a2 :: .formula a1 :: .context a0 :: s => some (.cert (.pc a0 a1 a2) :: s)
 | 12, .cert a3 :: .formula a2 :: .formula a1 :: .context a0 :: s => some (.cert (.ii a0 a1 a2 a3) :: s)
 | 13, .cert a4 :: .cert a3 :: .formula a2 :: .formula a1 :: .context a0 :: s => some (.cert (.ie a0 a1 a2 a3 a4) :: s)
 | 14, .cert a2 :: .formula a1 :: .context a0 :: s => some (.cert (.exp a0 a1 a2) :: s)
 | 15, .cert a4 :: .cert a3 :: .formula a2 :: .formula a1 :: .context a0 :: s => some (.cert (.ci a0 a1 a2 a3 a4) :: s)
 | 16, .cert a3 :: .formula a2 :: .formula a1 :: .context a0 :: s => some (.cert (.ce1 a0 a1 a2 a3) :: s)
 | 17, .cert a3 :: .formula a2 :: .formula a1 :: .context a0 :: s => some (.cert (.ce2 a0 a1 a2 a3) :: s)
 | 18, .cert a3 :: .formula a2 :: .formula a1 :: .context a0 :: s => some (.cert (.di1 a0 a1 a2 a3) :: s)
 | 19, .cert a3 :: .formula a2 :: .formula a1 :: .context a0 :: s => some (.cert (.di2 a0 a1 a2 a3) :: s)
 | 20, .cert a5 :: .cert a4 :: .formula a3 :: .formula a2 :: .formula a1 :: .context a0 :: s => some (.cert (.branchPair a0 a1 a2 a3 a4 a5) :: s)
 | 21, .cert a5 :: .cert a4 :: .formula a3 :: .formula a2 :: .formula a1 :: .context a0 :: s => some (.cert (.de a0 a1 a2 a3 a4 a5) :: s)
 | 22, .cert a3 :: .formula a2 :: .context a1 :: .context a0 :: s => some (.cert (.wk a0 a1 a2 a3) :: s)
 | 23, .cert a2 :: .formula a1 :: .context a0 :: s => some (.cert (.allI a0 a1 a2) :: s)
 | 24, .cert a3 :: .nat a2 :: .formula a1 :: .context a0 :: s => some (.cert (.allE a0 a1 a2 a3) :: s)
 | 25, .cert a3 :: .nat a2 :: .formula a1 :: .context a0 :: s => some (.cert (.exI a0 a1 a2 a3) :: s)
 | 26, .cert a4 :: .cert a3 :: .formula a2 :: .formula a1 :: .context a0 :: s => some (.cert (.exE a0 a1 a2 a3 a4) :: s)
 | 27, s => some (.witness .refl :: s)
 | 28, s => some (.witness .sym :: s)
 | 29, s => some (.witness .trans :: s)
 | 30, s => some (.witness .eqElem :: s)
 | 31, s => some (.witness .ext :: s)
 | 32, s => some (.witness .empty :: s)
 | 33, s => some (.witness .pair :: s)
 | 34, s => some (.witness .union :: s)
 | 35, s => some (.witness .power :: s)
 | 36, s => some (.witness .omega :: s)
 | 37, s => some (.witness .foundation :: s)
 | 38, .formula p :: .nat n :: s => some (.witness (.separation n p) :: s)
 | 39, .formula p :: .nat n :: s => some (.witness (.replacement n p) :: s)
 | 40, s => some (.witnesses [] :: s)
 | 41, .witnesses tail :: .witness head :: s => some (.witnesses (head :: tail) :: s)
 | _, _ => none

def step (token : Nat) (s : List Value) : Option (List Value) :=
 if token % 2 = 0 then some (.nat (token / 2) :: s)
 else instruction (token / 2) s

def run : List Nat → List Value → Option (List Value)
 | [], s => some s
 | token :: rest, s => step token s >>= run rest

theorem run_append (xs ys : List Nat) (s : List Value) :
 run (xs ++ ys) s = run xs s >>= run ys := by
 induction xs generalizing s with
 | nil => rfl
 | cons x xs ih =>
   simp only [List.cons_append, run]
   cases step x s with
   | none => rfl
   | some t => exact ih t

def emitNat (n : Nat) : List Nat := [2*n]
@[simp] theorem runNat (n : Nat) (s : List Value) :
 run (emitNat n) s = some (.nat n :: s) := by
 simp [emitNat, run, step, Nat.mul_div_right]

def emitFormula : Formula → List Nat
 | .bot  => [1]
 | .mem a0 a1 => emitNat a0 ++ emitNat a1 ++ [3]
 | .eq a0 a1 => emitNat a0 ++ emitNat a1 ++ [5]
 | .and a0 a1 => emitFormula a0 ++ emitFormula a1 ++ [7]
 | .or a0 a1 => emitFormula a0 ++ emitFormula a1 ++ [9]
 | .imp a0 a1 => emitFormula a0 ++ emitFormula a1 ++ [11]
 | .all a0 => emitFormula a0 ++ [13]
 | .ex a0 => emitFormula a0 ++ [15]

@[simp] theorem runFormula (a : Formula) (s : List Value) :
 run (emitFormula a) s = some (.formula a :: s) := by
 induction a generalizing s <;> simp_all only [emitFormula, run_append, runNat, Bind.bind, Option.bind_some] <;> rfl

def emitContext : Context → List Nat
 | [] => [17]
 | a :: rest => emitFormula a ++ emitContext rest ++ [19]

@[simp] theorem runContext (c : Context) (s : List Value) :
 run (emitContext c) s = some (.context c :: s) := by
 induction c generalizing s with
 | nil => rfl
 | cons a rest ih => simp only [emitContext, run_append, ih, runFormula, Bind.bind, Option.bind_some]; rfl

def emitCert : Executable.Cert → List Nat
 | .ctx a0 a1 => emitContext a0 ++ emitFormula a1 ++ [21]
 | .pc a0 a1 a2 => emitContext a0 ++ emitFormula a1 ++ emitFormula a2 ++ [23]
 | .ii a0 a1 a2 a3 => emitContext a0 ++ emitFormula a1 ++ emitFormula a2 ++ emitCert a3 ++ [25]
 | .ie a0 a1 a2 a3 a4 => emitContext a0 ++ emitFormula a1 ++ emitFormula a2 ++ emitCert a3 ++ emitCert a4 ++ [27]
 | .exp a0 a1 a2 => emitContext a0 ++ emitFormula a1 ++ emitCert a2 ++ [29]
 | .ci a0 a1 a2 a3 a4 => emitContext a0 ++ emitFormula a1 ++ emitFormula a2 ++ emitCert a3 ++ emitCert a4 ++ [31]
 | .ce1 a0 a1 a2 a3 => emitContext a0 ++ emitFormula a1 ++ emitFormula a2 ++ emitCert a3 ++ [33]
 | .ce2 a0 a1 a2 a3 => emitContext a0 ++ emitFormula a1 ++ emitFormula a2 ++ emitCert a3 ++ [35]
 | .di1 a0 a1 a2 a3 => emitContext a0 ++ emitFormula a1 ++ emitFormula a2 ++ emitCert a3 ++ [37]
 | .di2 a0 a1 a2 a3 => emitContext a0 ++ emitFormula a1 ++ emitFormula a2 ++ emitCert a3 ++ [39]
 | .branchPair a0 a1 a2 a3 a4 a5 => emitContext a0 ++ emitFormula a1 ++ emitFormula a2 ++ emitFormula a3 ++ emitCert a4 ++ emitCert a5 ++ [41]
 | .de a0 a1 a2 a3 a4 a5 => emitContext a0 ++ emitFormula a1 ++ emitFormula a2 ++ emitFormula a3 ++ emitCert a4 ++ emitCert a5 ++ [43]
 | .wk a0 a1 a2 a3 => emitContext a0 ++ emitContext a1 ++ emitFormula a2 ++ emitCert a3 ++ [45]
 | .allI a0 a1 a2 => emitContext a0 ++ emitFormula a1 ++ emitCert a2 ++ [47]
 | .allE a0 a1 a2 a3 => emitContext a0 ++ emitFormula a1 ++ emitNat a2 ++ emitCert a3 ++ [49]
 | .exI a0 a1 a2 a3 => emitContext a0 ++ emitFormula a1 ++ emitNat a2 ++ emitCert a3 ++ [51]
 | .exE a0 a1 a2 a3 a4 => emitContext a0 ++ emitFormula a1 ++ emitFormula a2 ++ emitCert a3 ++ emitCert a4 ++ [53]

@[simp] theorem runCert (a : Executable.Cert) (s : List Value) :
 run (emitCert a) s = some (.cert a :: s) := by
 induction a generalizing s <;> simp_all only [emitCert, run_append, runNat, runFormula, runContext, Bind.bind, Option.bind_some] <;> rfl

/-- Decode only complete singleton certificates; reject trailing values. -/
def decode (tokens : List Nat) : Option Executable.Cert := do
 match ← run tokens [] with
 | [.cert c] => some c
 | _ => none

@[simp] theorem decode_emit (c : Executable.Cert) :
 decode (emitCert c) = some c := by simp [decode]

/-- Exact checker after flat-token decoding. This stage is executable but not
claimed to be compiled to Code yet. -/
def check (tokens : List Nat) : Option Row := do
 let c ← decode tokens
 Executable.conclusion c

theorem check_emit (c : Executable.Cert) :
 check (emitCert c) = Executable.conclusion c := by simp [check]

theorem sound (tokens : List Nat) (r : Row) (h : check tokens = some r) : ND r := by
 unfold check at h
 cases hd : decode tokens with
 | none => simp [hd] at h
 | some c => exact Executable.sound c r (by simpa [hd] using h)

theorem complete {r : Row} (h : ND r) : ∃ tokens, check tokens = some r := by
 obtain ⟨c, hc⟩ := Executable.complete_checked h
 refine ⟨emitCert c, ?_⟩
 rw [check_emit]
 simp [Executable.conclusion, hc]

def emitWitness : ExecutableZF.AxiomWitness → List Nat
 | .refl => [55]
 | .sym => [57]
 | .trans => [59]
 | .eqElem => [61]
 | .ext => [63]
 | .empty => [65]
 | .pair => [67]
 | .union => [69]
 | .power => [71]
 | .omega => [73]
 | .foundation => [75]
 | .separation n p => emitNat n ++ emitFormula p ++ [77]
 | .replacement n p => emitNat n ++ emitFormula p ++ [79]

@[simp] theorem runWitness (w : ExecutableZF.AxiomWitness) (s : List Value) :
 run (emitWitness w) s = some (.witness w :: s) := by
 cases w <;> simp only [emitWitness, run_append, runNat, runFormula,
  Bind.bind, Option.bind_some] <;> rfl

def emitWitnesses : List ExecutableZF.AxiomWitness → List Nat
 | [] => [81]
 | a :: rest => emitWitness a ++ emitWitnesses rest ++ [83]

@[simp] theorem runWitnesses (ws : List ExecutableZF.AxiomWitness) (s : List Value) :
 run (emitWitnesses ws) s = some (.witnesses ws :: s) := by
 induction ws generalizing s with
 | nil => rfl
 | cons w ws ih =>
   simp only [emitWitnesses, run_append, runWitness, ih, Bind.bind, Option.bind_some]
   rfl

end ZFR.TokenVM
