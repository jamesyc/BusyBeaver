module
public import M207.SourceDefinitions
public import M207.LiteralFrames
@[expose] public section
namespace M207.Source
open M6.Zip M6.Runtime

def effectFile : Eff → List Nat → List Nat
  | .none, vs => vs
  | .inc r, vs => incr r vs ++ [1]
  | .dec r, vs => decr r vs

private theorem flat_bits (path : List Bool) (n : Nat) (vs : List Nat) :
    flat n vs (path.map Seg.bit) = path := by
  induction path with
  | nil => rfl
  | cons b path ih => simpa [flat,segList] using congrArg (b :: ·) ih

private theorem flat_append (a b : List Seg) (n : Nat) (vs : List Nat) :
    flat n vs (a ++ b) = flat n vs a ++ flat n vs b := by simp [flat]

theorem rootFrame_effect (path : List Bool) (hp : path.length ≤ 48)
    (extra n : Nat) (vs : List Nat) (effect : Eff) :
    conc n vs (rootFrame path extra effect) =
      conc (n + extra) (effectFile effect vs) (rootFrame path) := by
  have hlen : n + (48 + extra - path.length) = n + extra + (48 - path.length) := by omega
  simp only [rootFrame, conc, flat_append, flat_bits]
  cases effect <;> simp [flat, segList, boxList, effectFile, hlen]

def frameAt (path : List Bool) (n : Nat) (vs : List Nat) : Conf :=
  mapConf forward (conc n vs (rootFrame path))

def ImplementsCode (paths : Nat → List Bool) (path : List Bool) (code : Instruction) : Prop :=
  ∀ n vs, 10 ≤ vs.length →
    match execute code ⟨0,n,vs⟩ with
    | none => Halts literal (frameAt path n vs)
    | some t => Reach1 literal (frameAt path n vs) (frame paths t)

theorem contract_inc (paths : Nat → List Bool) (path : List Bool) (r k fuel : Nat)
    (hp : (paths k).length ≤ 48)
    (hc : (exec renamed none (fun s => sMatches s (rootFrame (paths k) 0 (.inc r)))
      fuel (rootFrame path) false).isSome = true) :
    ImplementsCode paths path (.inc r k) := by
  intro n vs hv
  have hr := literal_frame_certificate none fuel (rootFrame path)
    (rootFrame (paths k) 0 (.inc r)) hc n vs ⟨hv,trivial⟩
  rw [rootFrame_effect _ hp] at hr
  simpa [ImplementsCode,execute,frameAt,frame,effectFile] using hr

theorem contract_jump (paths : Nat → List Bool) (path : List Bool) (k fuel : Nat)
    (hc : (exec renamed none (fun s => sMatches s (rootFrame (paths k)))
      fuel (rootFrame path) false).isSome = true) :
    ImplementsCode paths path (.jump k) := by
  intro n vs hv
  exact literal_frame_certificate none fuel (rootFrame path)
    (rootFrame (paths k)) hc n vs ⟨hv,trivial⟩

theorem contract_dec (paths : Nat → List Bool) (path : List Bool) (r z p fz fp : Nat)
    (hp : (paths p).length ≤ 48)
    (cz : (exec renamed (some (r,true)) (fun s => sMatches s (rootFrame (paths z)))
      fz (rootFrame path) false).isSome = true)
    (cp : (exec renamed (some (r,false)) (fun s => sMatches s (rootFrame (paths p) 1 (.dec r)))
      fp (rootFrame path) false).isSome = true) :
    ImplementsCode paths path (.dec r z p) := by
  intro n vs hv
  by_cases hz : vs.getD r 0 = 0
  · have hr := literal_frame_certificate (some (r,true)) fz (rootFrame path)
      (rootFrame (paths z)) cz n vs ⟨hv,hz⟩
    simpa only [execute, hz, if_true, frameAt, frame] using hr
  · have hr := literal_frame_certificate (some (r,false)) fp (rootFrame path)
      (rootFrame (paths p) 1 (.dec r)) cp n vs ⟨hv,hz⟩
    rw [rootFrame_effect _ hp] at hr
    simpa only [execute, hz, if_false, frameAt, frame, effectFile] using hr

theorem contract_halt (paths : Nat → List Bool) (path : List Bool) (fuel : Nat)
    (hc : (exec renamed none (fun s => s.1 == inverse 207) fuel (rootFrame path) false).isSome = true) :
    ImplementsCode paths path .halt := by
  intro n vs hv
  exact literal_halt_certificate none fuel (rootFrame path) hc n vs ⟨hv,trivial⟩
end M207.Source
