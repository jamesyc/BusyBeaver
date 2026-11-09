module

public import PA211.UserCandidate.Dense
public import PA211.UserCandidate.StartupExact

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.LiteralStartup
open PA215.Zip

def inverseLabel (q : Nat) : Nat := Dense.labels.idxOf q
def inverseConf (c : Conf) : Conf := ⟨inverseLabel c.q,c.l,c.r⟩
private theorem inverse_check : (List.range 216).all (fun q =>
    decide (inverseLabel (Dense.label q) = q)) = true := by decide +kernel

theorem inverse_label {q : Nat} (hq : q < 216) : inverseLabel (Dense.label q) = q :=
  of_decide_eq_true (List.all_eq_true.mp inverse_check q (List.mem_range.mpr hq))

theorem inverse_map (c : Conf) (hq : c.q < 216) : inverseConf (Dense.mapConf c) = c := by
  rcases c with ⟨q,l,r⟩
  simp only [Dense.mapConf,inverseConf,inverse_label hq]

def target : Conf := inverseConf PA213.Startup.startupTarget

theorem target_control : target.q = 81 := by decide +kernel

theorem startup_exact : run Dense.machine 64764 (zc 0 [] []) = some target := by
  have hc := Dense.run_conjugate 64764 (zc 0 [] []) (by decide)
  change run CandidateTable.machine 64764 PA213.Startup.blank =
    (run Dense.machine 64764 (zc 0 [] [])).map Dense.mapConf at hc
  rw [Startup.startup_exact] at hc
  cases he : run Dense.machine 64764 (zc 0 [] []) with
  | none => rw [he] at hc; cases hc
  | some c =>
    rw [he] at hc
    have hm : PA213.Startup.startupTarget = Dense.mapConf c := Option.some.inj hc
    have hb := Dense.run_bounded (c := zc 0 [] []) (by decide) he
    have hi := congrArg inverseConf hm
    rw [inverse_map c hb] at hi
    exact congrArg some hi.symm

#print axioms startup_exact
end PA211.UserCandidate.LiteralStartup
