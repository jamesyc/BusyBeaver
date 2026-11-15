module
public import ModelReplay1965
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 1966 powS
theorem p1966 (a0 : M) (a1 : M)  : (t10 (M := M) (t117 (M := M) (a0) (t29 (M := M) (a1))) (t45 (M := M) (a0) (t117 (M := M) (a0) (a1)))) := by
  let e1  : M := (t117 (M := M) (a0) ((show M from (t29 (M := M) (a1)))))
  let e2 (u0 : M) : M := (t45 (M := M) (a0) u0)
  let e3  : (M → Prop) := (t82 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e4  : M := (t30 (M := M))
  let e6  : M := (t84 (M := M) (e3) ((show M from (t110 (M := M) (e4) (e3) (a1)))))
  let e7  : M := (t117 (M := M) (a0) (a1))
  let e8  : M := (t45 (M := M) (a0) (e7))
  let e9  : Prop := (t10 (M := M) (e1) (e6))
  let e10  : Prop := (t10 (M := M) (e6) (e8))
  let ee : Nat → M := fun _ => a0
  let multGraph : ZF209.MM0ModelPeano.FunctionGraphCertificate ee 1 (fun v => t45 (M := M) a0 (v 0)) := {
    formula := “y x. y=&0*x”
    correct := by intro v y; rfl
  }
  have v0 := p342 (M := M) (e1) (e6) (e8)
  have v1 := p1905 (M := M) ee (e4) (e3) (a1) (literalGraph_certificate (F := fun x => t45 (M := M) a0 x) multGraph)
  have v2 : (e9) := (show (e9) from v1)
  have v3 := ((v0) (v2))
  have v4 := fun z0 : M => p805 (M := M) (a0) z0 (e7)
  have v5 := p1494 (M := M) (e7) (e8) (fun w2 : M => (e2 w2)) ((fun w2 : M => v4 w2))
  have v6 : (e10) := (show (e10) from v5)
  have v7 := ((v3) (v6))
  exact v7
-- Actual MMB 1967 powS2
theorem p1967 (a0 : M) (a1 : M)  : (t10 (M := M) (t117 (M := M) (a0) (t29 (M := M) (a1))) (t45 (M := M) (t117 (M := M) (a0) (a1)) (a0))) := by
  let e1  : M := (t117 (M := M) (a0) ((show M from (t29 (M := M) (a1)))))
  let e2  : M := (t117 (M := M) (a0) (a1))
  let e3  : M := (t45 (M := M) (a0) (e2))
  let e4  : M := (t45 (M := M) (e2) (a0))
  let e6  : Prop := (t10 (M := M) (e3) (e4))
  let e7  : Prop := (t10 (M := M) (e1) (e4))
  have v0 := p342 (M := M) (e1) (e3) (e4)
  have v1 := p1966 (M := M) (a0) (a1)
  have v2 := b3 ((show Prop from (t10 (M := M) (e1) (e3)))) ((show Prop from (t0 (e6) (e7)))) (v0) (v1)
  have v3 := p827 (M := M) (a0) (e2)
  have v4 := b3 (e6) (e7) (v2) (v3)
  exact v4
-- Actual MMB 1968 pow12
theorem p1968 (a0 : M)  : (t10 (M := M) (t117 (M := M) (a0) (t30 (M := M))) (a0)) := by
  let e0  : M := (t30 (M := M))
  let e1  : M := (t117 (M := M) (a0) (e0))
  let e2  : M := (t28 (M := M))
  let e3  : M := (t117 (M := M) (a0) (e2))
  let e4  : M := (t45 (M := M) (a0) (e3))
  let e5  : Prop := (t10 (M := M) (e1) (e4))
  have v0 := p342 (M := M) (e1) (e4) (a0)
  have v1 := p1966 (M := M) (a0) (e2)
  have v2 : (e5) := (show (e5) from v1)
  have v3 := ((v0) (v2))
  have v4 := p342 (M := M) (e4) ((show M from (t45 (M := M) (a0) (e0)))) (a0)
  have v5 := p805 (M := M) (a0) (e3) (e0)
  have v6 := p1965 (M := M) (a0)
  have v7 := ((v5) (v6))
  have v8 := ((v4) (v7))
  have v9 := p828 (M := M) (a0)
  have v10 := ((v8) (v9))
  have v11 := ((v3) (v10))
  exact v11
-- Actual MMB 1969 pow22

end ZF209.MM0ModelReplay
