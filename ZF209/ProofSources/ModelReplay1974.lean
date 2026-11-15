module
public import ModelReplay1969
public import ModelLiteralPowerFunctionCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 1970 pow11
theorem p1971 (a0 : M) (a1 : M)  : (t0 (t48 (M := M) (t28 (M := M)) (a0)) (t48 (M := M) (t28 (M := M)) (t117 (M := M) (a0) (a1)))) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1  : M := (t28 (M := M))
  let e2 (u0 : M) : M := (t117 (M := M) (a0) u0)
  let e3  : M := (t117 (M := M) (a0) (a1))
  let e4 (u0 : M) : Prop := (t10 (M := M) u0 (e1))
  let e5  : M := (t117 (M := M) (a0) (e1))
  let e6 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e7 (u0 : M) : M := (t117 (M := M) (a0) u0)
  let e8 (u0 : M) : M := (t29 (M := M) u0)
  let e9 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (e8 u1))
  let e10 (u0 : M) : M := (t117 (M := M) (a0) (e8 u0))
  let e11  : M := (t30 (M := M))
  let e13  : Prop := (t48 (M := M) (e1) (e5))
  let e14  : Prop := (t48 (M := M) (e1) (e11))
  let e16  : Prop := (t48 (M := M) (e1) (a0))
  let e17 (u0 : M) : M := (t45 (M := M) (a0) (e7 u0))
  let e18 (u0 : M) : Prop := (t10 (M := M) (e10 u0) (e17 u0))
  let e19 (u0 : M) : Prop := (t48 (M := M) (e1) (e10 u0))
  let e20 (u0 : M) : Prop := (t48 (M := M) (e1) (e17 u0))
  let e21 (u0 : M) : Prop := (t3 (e19 u0) (e20 u0))
  let e22 (u0 : M) : Prop := (t48 (M := M) (e1) (e7 u0))
  let e23 (u0 : M) : Prop := (t2 (e16) (e22 u0))
  let e24 (u0 : M) : Prop := (t48 (M := M) (e1) (e2 u0))
  let e25  : Prop := (t48 (M := M) (e1) (e3))
  let ee : Nat → M := fun _ => a0
  let outputCertificate : ZF209.MM0ModelPeano.FormulaCertificate ee 2 (fun v => t48 (M := M) (t28 (M := M)) (v 0)) := {
    formula := “y x. ∃q, (1)+q=y”
    correct := by
      intro v
      classical
      simp [t48,t47,t29,t28,t9,t1,t8,t10,t44]
  }
  let inductionCertificate : ZF209.MM0ModelPeano.FormulaCertificate ee 1 (fun v => e24 (v 0)) :=
    (literalPowerFunction_certificate ee 0).substitute outputCertificate
  let antecedentCertificate : ZF209.MM0ModelPeano.FormulaCertificate ee 1 (fun _ => e16) := {
    formula := “∃q, (1)+q=&0”
    correct := by
      intro v
      classical
      simp [e16,e1,t30,t31,t48,t47,t29,t28,t9,t1,t8,t10,t44,ee]
  }
  have v0 := fun z0 : M => p8 (e0 z0)
  have v1 := fun z0 : M => p1963 (M := M) (e0 z0) (a0) z0 (a1) (v0 z0)
  have v2 := fun z0 : M => p890 (M := M) (e0 z0) (e1) (e2 z0) (e3) (v1 z0)
  have v3 := fun z0 : M => p8 (e4 z0)
  have v4 := fun z0 : M => p1963 (M := M) (e4 z0) (a0) z0 (e1) (v3 z0)
  have v5 := fun z0 : M => p890 (M := M) (e4 z0) (e1) (e2 z0) (e5) (v4 z0)
  have v6 := fun z0 : M => fun z1 : M => p8 (e6 z0 z1)
  have v7 := fun z0 : M => fun z1 : M => p1963 (M := M) (e6 z0 z1) (a0) z0 z1 (v6 z0 z1)
  have v8 := fun z0 : M => fun z1 : M => p890 (M := M) (e6 z0 z1) (e1) (e2 z0) (e7 z1) (v7 z0 z1)
  have v9 := fun z0 : M => fun z1 : M => p8 (e9 z0 z1)
  have v10 := fun z0 : M => fun z1 : M => p1963 (M := M) (e9 z0 z1) (a0) z0 (e8 z1) (v9 z0 z1)
  have v11 := fun z0 : M => fun z1 : M => p890 (M := M) (e9 z0 z1) (e1) (e2 z0) (e10 z1) (v10 z0 z1)
  have v12 := p891 (M := M) (e1) (e5) (e11)
  have v13 := p1965 (M := M) (a0)
  have v14 := ((v12) (v13))
  have v15 := p918 (M := M)
  have v16 := p118 (e14) (e13) (v14) (v15)
  have v17 := p4 (e16) (e13) (v16)
  have v18 := fun z0 : M => p891 (M := M) (e1) (e10 z0) (e17 z0)
  have v19 := fun z0 : M => p1966 (M := M) (a0) z0
  have v20 := fun z0 : M => ((v18 z0) (v19 z0))
  have v21 := fun z0 : M => p960 (M := M) (a0) (e7 z0)
  have v22 := fun z0 : M => p109 (e20 z0) (e23 z0) (v21 z0)
  have v23 := fun z0 : M => p154 (e23 z0) (e20 z0) (e19 z0) (v20 z0) (v22 z0)
  have v24 := p742 (M := M) ee (e16) (fun w2 : M => (a1)) (fun w1 : M => (e24 w1)) (fun w2 : M => (e13)) (fun w2 : M => (e25)) (fun w2 : M => (e22 w2)) (fun w2 : M => (e19 w2)) antecedentCertificate inductionCertificate ((fun w1 : M => (fun w2 : M => v2 w1))) ((fun w1 : M => (fun w2 : M => v5 w1))) ((fun w1 : M => (fun w2 : M => v8 w1 w2))) ((fun w1 : M => (fun w2 : M => v11 w1 w2))) ((fun w2 : M => v17)) ((fun w2 : M => v23 w2)) 0
  exact v24
-- Actual MMB 1972 powne0
theorem p1972 (a0 : M) (a1 : M)  : (t0 (t13 (M := M) (a0) (t28 (M := M))) (t13 (M := M) (t117 (M := M) (a0) (a1)) (t28 (M := M)))) := by
  let e0  : M := (t117 (M := M) (a0) (a1))
  let e1  : M := (t28 (M := M))
  let e2  : Prop := (t48 (M := M) (e1) (a0))
  let e4  : Prop := (t13 (M := M) (e0) (e1))
  have v0 := p903 (M := M) (a0)
  have v1 := p903 (M := M) (e0)
  have v2 := p1971 (M := M) (a0) (a1)
  have v3 := p153 (e2) ((show Prop from (t48 (M := M) (e1) (e0)))) (e4) (v1) (v2)
  have v4 := p156 ((show Prop from (t13 (M := M) (a0) (e1)))) (e2) (e4) (v0) (v3)
  exact v4
-- Actual MMB 1973 pow2ne0
theorem p1973 (a0 : M)  : (t13 (M := M) (t117 (M := M) (t31 (M := M)) (a0)) (t28 (M := M))) := by
  let e0  : M := (t31 (M := M))
  let e1  : M := (t28 (M := M))
  have v0 := p1972 (M := M) (e0) (a0)
  have v1 := p738 (M := M)
  have v2 := b3 ((show Prop from (t13 (M := M) (e0) (e1)))) ((show Prop from (t13 (M := M) ((show M from (t117 (M := M) (e0) (a0)))) (e1)))) (v0) (v1)
  exact v2
-- Actual MMB 1974 powltid2
theorem p1974 (a0 : M) (a1 : M)  : (t0 (t48 (M := M) (t30 (M := M)) (a0)) (t48 (M := M) (a1) (t117 (M := M) (a0) (a1)))) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : M := (t117 (M := M) (a0) u0)
  let e2  : M := (t117 (M := M) (a0) (a1))
  let e3  : M := (t28 (M := M))
  let e4 (u0 : M) : Prop := (t10 (M := M) u0 (e3))
  let e5  : M := (t117 (M := M) (a0) (e3))
  let e6 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e7 (u0 : M) : M := (t117 (M := M) (a0) u0)
  let e8 (u0 : M) : M := (t29 (M := M) u0)
  let e9 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (e8 u1))
  let e10 (u0 : M) : M := (t117 (M := M) (a0) (e8 u0))
  let e11  : M := (t30 (M := M))
  let e13  : Prop := (t48 (M := M) (e3) (e5))
  let e14  : Prop := (t48 (M := M) (e3) (e11))
  let e16  : Prop := (t48 (M := M) (e11) (a0))
  let e17 (u0 : M) : Prop := (t48 (M := M) u0 (e7 u0))
  let e18 (u0 : M) : Prop := (t2 (e16) (e17 u0))
  let e19 (u0 : M) : Prop := (t47 (M := M) (e8 u0) (e7 u0))
  let e20 (u0 : M) : Prop := (t0 (e18 u0) (e19 u0))
  let e21 (u0 : M) : M := (t45 (M := M) (e11) (e7 u0))
  let e22 (u0 : M) : M := (t45 (M := M) (a0) (e7 u0))
  let e23 (u0 : M) : Prop := (t10 (M := M) (e21 u0) (e7 u0))
  let e24 (u0 : M) : Prop := (t10 (M := M) (e22 u0) (e10 u0))
  let e25 (u0 : M) : Prop := (t48 (M := M) (e21 u0) (e22 u0))
  let e26 (u0 : M) : Prop := (t48 (M := M) (e7 u0) (e10 u0))
  let e27 (u0 : M) : Prop := (t3 (e25 u0) (e26 u0))
  let e28 (u0 : M) : Prop := (t0 (e24 u0) (e27 u0))
  let e29 (u0 : M) : Prop := (t10 (M := M) (e10 u0) (e22 u0))
  let e30  : Prop := (t48 (M := M) (e3) (a0))
  let e32 (u0 : M) : Prop := (t48 (M := M) (e3) (e7 u0))
  let e33 (u0 : M) : Prop := (t3 (e16) (e25 u0))
  let e34 (u0 : M) : Prop := (t48 (M := M) u0 (e1 u0))
  let e35  : Prop := (t48 (M := M) (a1) (e2))
  let e36 (u0 : M) : Prop := (t48 (M := M) (e8 u0) (e10 u0))
  let ee : Nat → M := fun _ => a0
  let outputCertificate : ZF209.MM0ModelPeano.FormulaCertificate ee 2 (fun v => t48 (M := M) (v 1) (v 0)) := {
    formula := “y x. ∃q, (x+1)+q=y”
    correct := by
      intro v
      classical
      simp [t48,t47,t29,t28,t9,t1,t8,t10,t44]
  }
  let inductionCertificate : ZF209.MM0ModelPeano.FormulaCertificate ee 1 (fun v => e34 (v 0)) :=
    (literalPowerFunction_certificate ee 0).substitute outputCertificate
  let antecedentCertificate : ZF209.MM0ModelPeano.FormulaCertificate ee 1 (fun _ => e16) := {
    formula := “∃q, (1+1)+q=&0”
    correct := by
      intro v
      classical
      simp [e16,e11,e3,t30,t31,t48,t47,t29,t28,t9,t1,t8,t10,t44,ee]
  }
  have v0 := fun z0 : M => p8 (e0 z0)
  have v1 := fun z0 : M => p1963 (M := M) (e0 z0) (a0) z0 (a1) (v0 z0)
  have v2 := fun z0 : M => p886 (M := M) (e0 z0) z0 (a1) (e1 z0) (e2) (v0 z0) (v1 z0)
  have v3 := fun z0 : M => p8 (e4 z0)
  have v4 := fun z0 : M => p1963 (M := M) (e4 z0) (a0) z0 (e3) (v3 z0)
  have v5 := fun z0 : M => p886 (M := M) (e4 z0) z0 (e3) (e1 z0) (e5) (v3 z0) (v4 z0)
  have v6 := fun z0 : M => fun z1 : M => p8 (e6 z0 z1)
  have v7 := fun z0 : M => fun z1 : M => p1963 (M := M) (e6 z0 z1) (a0) z0 z1 (v6 z0 z1)
  have v8 := fun z0 : M => fun z1 : M => p886 (M := M) (e6 z0 z1) z0 z1 (e1 z0) (e7 z1) (v6 z0 z1) (v7 z0 z1)
  have v9 := fun z0 : M => fun z1 : M => p8 (e9 z0 z1)
  have v10 := fun z0 : M => fun z1 : M => p1963 (M := M) (e9 z0 z1) (a0) z0 (e8 z1) (v9 z0 z1)
  have v11 := fun z0 : M => fun z1 : M => p886 (M := M) (e9 z0 z1) z0 (e8 z1) (e1 z0) (e10 z1) (v9 z0 z1) (v10 z0 z1)
  have v12 := p891 (M := M) (e3) (e5) (e11)
  have v13 := p1965 (M := M) (a0)
  have v14 := ((v12) (v13))
  have v15 := p918 (M := M)
  have v16 := p118 (e14) (e13) (v14) (v15)
  have v17 := p4 (e16) (e13) (v16)
  have v18 := fun z0 : M => p54 (e16) (e17 z0)
  have v19 : (∀ z0 : M, (e20 z0)) := (show (∀ z0 : M, (e20 z0)) from v18)
  have v20 := fun z0 : M => p887 (M := M) (e21 z0) (e7 z0) (e22 z0) (e10 z0)
  have v21 := fun z0 : M => p829 (M := M) (e7 z0)
  have v22 := fun z0 : M => ((v20 z0) (v21 z0))
  have v23 := fun z0 : M => p341 (M := M) (e10 z0) (e22 z0)
  have v24 := fun z0 : M => p1966 (M := M) (a0) z0
  have v25 := fun z0 : M => ((v23 z0) (v24 z0))
  have v26 := fun z0 : M => ((v22 z0) (v25 z0))
  have v27 := fun z0 : M => p953 (M := M) (e11) (a0) (e7 z0)
  have v28 := fun z0 : M => p1971 (M := M) (a0) z0
  have v29 := p899 (M := M) (e3) (e11) (a0)
  have v30 := ((v29) (v15))
  have v31 := fun z0 : M => p62 (e16) (e17 z0) (e30) (v30)
  have v32 := fun z0 : M => p10 (e18 z0) (e30) (e32 z0) (v28 z0) (v31 z0)
  have v33 := fun z0 : M => p10 (e18 z0) (e32 z0) (e33 z0) (v27 z0) (v32 z0)
  have v34 := fun z0 : M => p53 (e16) (e17 z0)
  have v35 := fun z0 : M => p119 (e18 z0) (e16) (e25 z0) (v33 z0) (v34 z0)
  have v36 := fun z0 : M => p153 (e18 z0) (e25 z0) (e26 z0) (v26 z0) (v35 z0)
  have v37 := fun z0 : M => p898 (M := M) (e18 z0) (e8 z0) (e7 z0) (e10 z0) (v19 z0) (v36 z0)
  have v38 := p742 (M := M) ee (e16) (fun w2 : M => (a1)) (fun w1 : M => (e34 w1)) (fun w2 : M => (e13)) (fun w2 : M => (e35)) (fun w2 : M => (e17 w2)) (fun w2 : M => (e36 w2)) antecedentCertificate inductionCertificate ((fun w1 : M => (fun w2 : M => v2 w1))) ((fun w1 : M => (fun w2 : M => v5 w1))) ((fun w1 : M => (fun w2 : M => v8 w1 w2))) ((fun w1 : M => (fun w2 : M => v11 w1 w2))) ((fun w2 : M => v17)) ((fun w2 : M => v37 w2)) 0
  exact v38

end ZF209.MM0ModelReplay
