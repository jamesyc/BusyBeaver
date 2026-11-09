module

public import PA215.Source.RootFrame
public import PA215.OriginalCensusTypes

@[expose] public section

/-! Primitive obligations generated directly from the source operation/path.
No target frame is borrowed from a separately generated target census. -/
namespace PA215.Source
open PA215.Runtime PA215.Census

structure TargetPlan where
  path : Path
  extra : Nat
  effect : Eff
  deriving DecidableEq, Repr

def nextPlan (p : Path) (extra : Nat) (effect : Eff) : TargetPlan :=
  match successor p with
  | none => ⟨[], extra + 1, effect⟩
  | some q => ⟨q, extra, effect⟩

/-- Outer failure means malformed branch/path; inner none means explicit halt. -/
def targetPlan (s : Site) (branch : Branch) : Option (Option TargetPlan) :=
  match s.op, branch with
  | .inc r, none => some (some (nextPlan s.path 0 (.inc (physicalRegister r))))
  | .dec r, some (p,z) =>
      if p ≠ physicalRegister r then none
      else if z then do
        let path ← cut s.path false 1
        return some (nextPlan path 0 .none)
      else some (some (nextPlan s.path 1 (.dec p)))
  | .breakTo k, none => do
      let path ← cut s.path false k
      return some (nextPlan path 0 .none)
  | .continueTo k, none => do
      let path ← cut s.path true k
      return some ⟨path,0,.none⟩
  | .halt, none => some none
  | _, _ => none

def sourceTagArg : Op → String × Option Nat
  | .inc r => ("EInc",some r.val)
  | .dec r => ("EDecnz",some r.val)
  | .breakTo k => ("EBreak",some k)
  | .continueTo k => ("EContinue",some k)
  | .halt => ("EHalt",none)

/-- Exact metadata, branch, initial full frame and generated target full frame. -/
def agreesWith (s : Site) (r : RawOriginal) : Bool :=
  r.path == s.path && (r.tag,r.arg) == sourceTagArg s.op &&
  sMatches r.initial (rootFrame s.path) &&
  match targetPlan s r.branch, r.target with
  | some none, none => r.isHalt
  | some (some p), some t =>
      !r.isHalt && (p.path.length ≤ 64) &&
      sMatches t (rootFrame p.path p.extra p.effect)
  | _, _ => false

/-- An accepted comparison identifies the entire initial frame for every
padding value and every file, without requiring execution of the machine. -/
theorem agrees_initial (h : agreesWith s r = true) (n : Nat) (vs : List Nat) :
    conc n vs r.initial = conc n vs (rootFrame s.path) := by
  simp only [agreesWith, Bool.and_eq_true] at h
  exact sMatches_conc n vs h.1.2

/-- The generated nonterminal destination keeps all padding and spare cells. -/
theorem agrees_target (h : agreesWith s r = true)
    (hp : targetPlan s r.branch = some (some p)) (ht : r.target = some t)
    (n : Nat) (vs : List Nat) :
    conc n vs t = conc (n+p.extra) (effectFile p.effect vs) (rootFrame p.path) := by
  simp only [agreesWith, hp, ht, Bool.and_eq_true] at h
  exact (sMatches_conc n vs h.2.2).trans (rootFrame_effect p.path (of_decide_eq_true h.2.1.2) p.extra n vs p.effect)

#print axioms agrees_initial
#print axioms agrees_target
end PA215.Source
