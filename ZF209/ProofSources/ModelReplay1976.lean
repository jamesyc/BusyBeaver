module
public import ModelReplay1974
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 1975 powadd
theorem p1975 (a0 : M) (a1 : M) (a2 : M)  : (t10 (M := M) (t117 (M := M) (a0) (t44 (M := M) (a1) (a2))) (t45 (M := M) (t117 (M := M) (a0) (a1)) (t117 (M := M) (a0) (a2)))) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e1 (u0 : M) : M := (t44 (M := M) (a1) u0)
  let e2  : M := (t44 (M := M) (a1) (a2))
  let e3  : M := (t117 (M := M) (a0) (a1))
  let e4 (u0 : M) : M := (t117 (M := M) (a0) u0)
  let e5  : M := (t117 (M := M) (a0) (a2))
  let e6 (u0 : M) : M := (t117 (M := M) (a0) (e1 u0))
  let e7  : M := (t117 (M := M) (a0) (e2))
  let e8 (u0 : M) : M := (t45 (M := M) (e3) (e4 u0))
  let e9  : M := (t45 (M := M) (e3) (e5))
  let e10  : M := (t28 (M := M))
  let e11 (u0 : M) : Prop := (t10 (M := M) u0 (e10))
  let e12  : M := (t44 (M := M) (a1) (e10))
  let e13  : M := (t117 (M := M) (a0) (e10))
  let e14  : M := (t117 (M := M) (a0) (e12))
  let e15  : M := (t45 (M := M) (e3) (e13))
  let e16 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e17 (u0 : M) : M := (t44 (M := M) (a1) u0)
  let e18 (u0 : M) : M := (t117 (M := M) (a0) u0)
  let e19 (u0 : M) : M := (t117 (M := M) (a0) (e17 u0))
  let e20 (u0 : M) : M := (t45 (M := M) (e3) (e18 u0))
  let e21 (u0 : M) : M := (t29 (M := M) u0)
  let e22 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (e21 u1))
  let e23 (u0 : M) : M := (t44 (M := M) (a1) (e21 u0))
  let e24 (u0 : M) : M := (t117 (M := M) (a0) (e21 u0))
  let e25 (u0 : M) : M := (t117 (M := M) (a0) (e23 u0))
  let e26 (u0 : M) : M := (t45 (M := M) (e3) (e24 u0))
  let e32  : M := (t30 (M := M))
  let e38 (u0 : M) : M := (t29 (M := M) (e17 u0))
  let e39 (u0 : M) : Prop := (t10 (M := M) (e23 u0) (e38 u0))
  let e40 (u0 : M) : M := (t117 (M := M) (a0) (e38 u0))
  let e41 (u0 : M) : Prop := (t10 (M := M) (e25 u0) (e40 u0))
  let e42 (u0 : M) : M := (t45 (M := M) (e18 u0) (a0))
  let e43 (u0 : M) : Prop := (t10 (M := M) (e24 u0) (e42 u0))
  let e44 (u0 : M) : M := (t45 (M := M) (e3) (e42 u0))
  let e45 (u0 : M) : Prop := (t10 (M := M) (e26 u0) (e44 u0))
  let e46 (u0 : M) : Prop := (t10 (M := M) (e19 u0) (e20 u0))
  let e47 (u0 : M) : M := (t45 (M := M) (e19 u0) (a0))
  let e48 (u0 : M) : M := (t45 (M := M) (e20 u0) (a0))
  let e49 (u0 : M) : Prop := (t10 (M := M) (e6 u0) (e8 u0))
  let e51 (u0 : M) : Prop := (t10 (M := M) (e25 u0) (e26 u0))
  let ee : Nat → M := fun i => Nat.casesOn i a0 (fun i => Nat.casesOn i a1 (fun _ => t117 (M := M) a0 a1))
  let inputGraph : ZF209.MM0ModelPeano.FunctionGraphCertificate ee 1 (fun v => a1+v 0) := {
    formula := “y x. y=&1+x”
    correct := by intro v y; rfl
  }
  let powGraph := literalPowerFunction_certificate ee 0
  let leftGraph := powGraph.compose (G := fun x => a1+x) inputGraph
  let multGraph : ZF209.MM0ModelPeano.FunctionGraphCertificate ee 1 (fun v => (t117 (M := M) a0 a1)*v 0) := {
    formula := “y x. y=&2*x”
    correct := by intro v y; rfl
  }
  let rightGraph := multGraph.compose (F := fun x => (t117 (M := M) a0 a1)*x) (G := fun x => t117 (M := M) a0 x) powGraph
  let inductionCertificate : ZF209.MM0ModelPeano.FormulaCertificate ee 1 (fun v => e49 (v 0)) :=
    leftGraph.equal rightGraph
  have v0 := fun z0 : M => p8 (e0 z0)
  have v1 := fun z0 : M => p800 (M := M) (e0 z0) (a1) z0 (a2) (v0 z0)
  have v2 := fun z0 : M => p1963 (M := M) (e0 z0) (a0) (e1 z0) (e2) (v1 z0)
  have v3 := fun z0 : M => p1963 (M := M) (e0 z0) (a0) z0 (a2) (v0 z0)
  have v4 := fun z0 : M => p804 (M := M) (e0 z0) (e3) (e4 z0) (e5) (v3 z0)
  have v5 := fun z0 : M => p350 (M := M) (e0 z0) (e6 z0) (e7) (e8 z0) (e9) (v2 z0) (v4 z0)
  have v6 := fun z0 : M => p8 (e11 z0)
  have v7 := fun z0 : M => p800 (M := M) (e11 z0) (a1) z0 (e10) (v6 z0)
  have v8 := fun z0 : M => p1963 (M := M) (e11 z0) (a0) (e1 z0) (e12) (v7 z0)
  have v9 := fun z0 : M => p1963 (M := M) (e11 z0) (a0) z0 (e10) (v6 z0)
  have v10 := fun z0 : M => p804 (M := M) (e11 z0) (e3) (e4 z0) (e13) (v9 z0)
  have v11 := fun z0 : M => p350 (M := M) (e11 z0) (e6 z0) (e14) (e8 z0) (e15) (v8 z0) (v10 z0)
  have v12 := fun z0 : M => fun z1 : M => p8 (e16 z0 z1)
  have v13 := fun z0 : M => fun z1 : M => p800 (M := M) (e16 z0 z1) (a1) z0 z1 (v12 z0 z1)
  have v14 := fun z0 : M => fun z1 : M => p1963 (M := M) (e16 z0 z1) (a0) (e1 z0) (e17 z1) (v13 z0 z1)
  have v15 := fun z0 : M => fun z1 : M => p1963 (M := M) (e16 z0 z1) (a0) z0 z1 (v12 z0 z1)
  have v16 := fun z0 : M => fun z1 : M => p804 (M := M) (e16 z0 z1) (e3) (e4 z0) (e18 z1) (v15 z0 z1)
  have v17 := fun z0 : M => fun z1 : M => p350 (M := M) (e16 z0 z1) (e6 z0) (e19 z1) (e8 z0) (e20 z1) (v14 z0 z1) (v16 z0 z1)
  have v18 := fun z0 : M => fun z1 : M => p8 (e22 z0 z1)
  have v19 := fun z0 : M => fun z1 : M => p800 (M := M) (e22 z0 z1) (a1) z0 (e21 z1) (v18 z0 z1)
  have v20 := fun z0 : M => fun z1 : M => p1963 (M := M) (e22 z0 z1) (a0) (e1 z0) (e23 z1) (v19 z0 z1)
  have v21 := fun z0 : M => fun z1 : M => p1963 (M := M) (e22 z0 z1) (a0) z0 (e21 z1) (v18 z0 z1)
  have v22 := fun z0 : M => fun z1 : M => p804 (M := M) (e22 z0 z1) (e3) (e4 z0) (e24 z1) (v21 z0 z1)
  have v23 := fun z0 : M => fun z1 : M => p350 (M := M) (e22 z0 z1) (e6 z0) (e25 z1) (e8 z0) (e26 z1) (v20 z0 z1) (v22 z0 z1)
  have v24 := p344 (M := M) (e14) (e3) (e15)
  have v25 := p1964 (M := M) (a0) (e12) (a1)
  have v26 := b792 (M := M) (a1)
  have v27 := ((v25) (v26))
  have v28 := ((v24) (v27))
  have v29 := p342 (M := M) (e15) ((show M from (t45 (M := M) (e3) (e32)))) (e3)
  have v30 := p805 (M := M) (e3) (e13) (e32)
  have v31 := p1965 (M := M) (a0)
  have v32 := ((v30) (v31))
  have v33 := ((v29) (v32))
  have v34 := p828 (M := M) (e3)
  have v35 := ((v33) (v34))
  have v36 := ((v28) (v35))
  have v37 := fun z0 : M => p1964 (M := M) (a0) (e23 z0) (e38 z0)
  have v38 := fun z0 : M => b793 (M := M) (a1) z0
  have v39 := fun z0 : M => ((v37 z0) (v38 z0))
  have v40 := fun z0 : M => p805 (M := M) (e3) (e24 z0) (e42 z0)
  have v41 := fun z0 : M => p1967 (M := M) (a0) z0
  have v42 := fun z0 : M => ((v40 z0) (v41 z0))
  have v43 := fun z0 : M => p1967 (M := M) (a0) (e17 z0)
  have v44 := fun z0 : M => p834 (M := M) (e3) (e18 z0) (a0)
  have v45 := fun z0 : M => p803 (M := M) (e19 z0) (e20 z0) (a0)
  have v46 := fun z0 : M => p362 (M := M) (e46 z0) (e47 z0) (e48 z0) (e44 z0) (v44 z0) (v45 z0)
  have v47 := fun z0 : M => p360 (M := M) (e46 z0) (e40 z0) (e47 z0) (e44 z0) (v43 z0) (v46 z0)
  have v48 := fun z0 : M => p365 (M := M) (e46 z0) (e40 z0) (e44 z0) (e25 z0) (e26 z0) (v39 z0) (v42 z0) (v47 z0)
  have v49 := p741 (M := M) ee (fun w1 : M => (a2)) (fun w0 : M => (e49 w0)) (fun w1 : M => ((show Prop from (t10 (M := M) (e14) (e15))))) (fun w1 : M => ((show Prop from (t10 (M := M) (e7) (e9))))) (fun w1 : M => (e46 w1)) (fun w1 : M => (e51 w1)) inductionCertificate ((fun w0 : M => (fun w1 : M => v5 w0))) ((fun w0 : M => (fun w1 : M => v11 w0))) ((fun w0 : M => (fun w1 : M => v17 w0 w1))) ((fun w0 : M => (fun w1 : M => v23 w0 w1))) ((fun w1 : M => v36)) ((fun w1 : M => v48 w1)) 0
  exact v49
-- Actual MMB 1976 powmul

end ZF209.MM0ModelReplay
