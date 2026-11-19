module
public import DirectReturnValue
@[expose] public section
namespace RosserDirect.FourStack
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive K where
 | stream | data | scratch | output
 deriving DecidableEq, Fintype, Inhabited
abbrev Stmt4 (L : Type) := TM2.Stmt (fun _ : K => Symbol) L (Option Symbol)
abbrev Cfg4 (L : Type) := TM2.Cfg (fun _ : K => Symbol) L (Option Symbol)
def store4 (p a s c : List Symbol) : K → List Symbol
 | .stream => p | .data => a | .scratch => s | .output => c
def cfg4 {L : Type} (q : L) (v : Option Symbol) (p a s c : List Symbol) : Cfg4 L :=
 ⟨some q,v,store4 p a s c⟩

def dataRoles : Stack → K
 | .input => .data | .scratch => .scratch | .output => .output
def readRoles : Stack → K
 | .input => .stream | .scratch => .scratch | .output => .data
def outputRoles : Stack → K
 | .input => .output | .scratch => .scratch | .output => .data
def prepareRoles : Stack → K
 | .input => .data | .scratch => .scratch | .output => .stream

theorem data_injective : Function.Injective dataRoles := by intro a b h; cases a <;> cases b <;> simp_all [dataRoles]
theorem read_injective : Function.Injective readRoles := by intro a b h; cases a <;> cases b <;> simp_all [readRoles]
theorem output_injective : Function.Injective outputRoles := by intro a b h; cases a <;> cases b <;> simp_all [outputRoles]
theorem prepare_injective : Function.Injective prepareRoles := by intro a b h; cases a <;> cases b <;> simp_all [prepareRoles]

theorem embed_data {L Q : Type} (labels : L → Q) (q : L) (v : Option Symbol) (p a s c : List Symbol) :
 Routine.embed dataRoles labels (config q v a s c) (fun _ => p) = cfg4 (labels q) v p a s c := by
 unfold Routine.embed config cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_read {L Q : Type} (labels : L → Q) (q : L) (v : Option Symbol) (p a s c : List Symbol) :
 Routine.embed readRoles labels (config q v p s a) (fun _ => c) = cfg4 (labels q) v p a s c := by
 unfold Routine.embed config cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_output {L Q : Type} (labels : L → Q) (q : L) (v : Option Symbol) (p a s c : List Symbol) :
 Routine.embed outputRoles labels (config q v c s a) (fun _ => p) = cfg4 (labels q) v p a s c := by
 unfold Routine.embed config cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_prepare {L Q : Type} (labels : L → Q) (q : L) (v : Option Symbol) (p a s c : List Symbol) :
 Routine.embed prepareRoles labels (config q v a s p) (fun _ => c) = cfg4 (labels q) v p a s c := by
 unfold Routine.embed config cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl


theorem related_identity {L Q : Type} (labels : L → Q) (q : L) (v : Option Symbol)
 (p a s c : List Symbol) (d : Cfg4 Q)
 (h : Routine.Related id labels (cfg4 q v p a s c) d) : d = cfg4 (labels q) v p a s c := by
 rcases d with ⟨l,w,S⟩
 rcases h with ⟨hl,hv,hs⟩
 change l = some (labels q) at hl
 change w = v at hv
 change S = store4 p a s c at hs
 subst l; subst w; subst S
 rfl

theorem relabel_run {L Q : Type} (labels : L → Q)
 (M : L → Stmt4 L) (N : Q → Stmt4 Q)
 (agree : ∀ q, M q ≠ .halt → N (labels q) = Routine.relocate id labels (M q))
 (q r : L) (v w : Option Symbol) (p a s c p' a' s' c' : List Symbol)
 (h : TM2.Reaches M (cfg4 q v p a s c) (cfg4 r w p' a' s' c')) :
 TM2.Reaches N (cfg4 (labels q) v p a s c) (cfg4 (labels r) w p' a' s' c') := by
 obtain ⟨d,hd,hr,he⟩ := Routine.lift_run id Function.injective_id labels M N agree h
   (by simp [cfg4]) (show Routine.Related id labels (cfg4 q v p a s c) (cfg4 (labels q) v p a s c) from ⟨rfl,rfl,rfl⟩)
 rw [related_identity labels r w p' a' s' c' d hr] at hd
 exact hd

end RosserDirect.FourStack
