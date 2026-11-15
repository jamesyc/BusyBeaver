module
public import ModelReplay808
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 809 add01
theorem p809 (a0 : M)  : (t10 (t44 (t28) (a0)) (a0)) := by
  let e0  : M := (t28)
  let e1 (u0 : M) : Prop := (t10 u0 (a0))
  let e2 (u0 : M) : M := (t44 (e0) u0)
  let e3  : M := (t44 (e0) (a0))
  let e4 (u0 : M) : Prop := (t10 u0 (e0))
  let e5  : M := (t44 (e0) (e0))
  let e6 (u0 : M) (u1 : M) : Prop := (t10 u0 u1)
  let e7 (u0 : M) : M := (t44 (e0) u0)
  let e8 (u0 : M) : M := (t29 u0)
  let e9 (u0 : M) (u1 : M) : Prop := (t10 u0 (e8 u1))
  let e10 (u0 : M) : M := (t44 (e0) (e8 u0))
  let e11 (u0 : M) : Prop := (t10 (e7 u0) u0)
  let e12 (u0 : M) : M := (t29 (e7 u0))
  let e13 (u0 : M) : Prop := (t10 (e2 u0) u0)
  let e14  : Prop := (t10 (e5) (e0))
  let e15  : Prop := (t10 (e3) (a0))
  let e16 (u0 : M) : Prop := (t10 (e10 u0) (e8 u0))
  let certificate : ZF209.MM0ModelPeano.FormulaCertificate (fun _ : Nat => (0:M)) 1 (fun v => e13 (v 0)) := {
    formula := “x. 0+x=x”
    correct := by intro v; simp [e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,t0,t1,t8,t9,t10,t13,t28,t29,t44]
  }
  have v0 := fun z0 : M => p801 (e0) z0 (a0)
  have v1 := fun z0 : M => p8 (e1 z0)
  have v2 := fun z0 : M => p350 (e1 z0) (e2 z0) (e3) z0 (a0) (v0 z0) (v1 z0)
  have v3 := fun z0 : M => p801 (e0) z0 (e0)
  have v4 := fun z0 : M => p8 (e4 z0)
  have v5 := fun z0 : M => p350 (e4 z0) (e2 z0) (e5) z0 (e0) (v3 z0) (v4 z0)
  have v6 := fun z0 : M => fun z1 : M => p801 (e0) z0 z1
  have v7 := fun z0 : M => fun z1 : M => p8 (e6 z0 z1)
  have v8 := fun z0 : M => fun z1 : M => p350 (e6 z0 z1) (e2 z0) (e7 z1) z0 z1 (v6 z0 z1) (v7 z0 z1)
  have v9 := fun z0 : M => fun z1 : M => p801 (e0) z0 (e8 z1)
  have v10 := fun z0 : M => fun z1 : M => p8 (e9 z0 z1)
  have v11 := fun z0 : M => fun z1 : M => p350 (e9 z0 z1) (e2 z0) (e10 z1) z0 (e8 z1) (v9 z0 z1) (v10 z0 z1)
  have v12 := b792 (e0)
  have v13 := fun z0 : M => b793 (e0) z0
  have v14 := fun z0 : M => p739 (e7 z0) z0
  have v15 := fun z0 : M => p360 (e11 z0) (e10 z0) (e12 z0) (e8 z0) (v13 z0) (v14 z0)
  have v16 := p741 (fun _ : Nat => (0:M)) (fun w1 : M => (a0)) (fun w0 : M => (e13 w0)) (fun w1 : M => (e14)) (fun w1 : M => (e15)) (fun w1 : M => (e11 w1)) (fun w1 : M => (e16 w1)) certificate ((fun w0 : M => (fun w1 : M => v2 w0))) ((fun w0 : M => (fun w1 : M => v5 w0))) ((fun w0 : M => (fun w1 : M => v8 w0 w1))) ((fun w0 : M => (fun w1 : M => v11 w0 w1))) ((fun w1 : M => v12)) ((fun w1 : M => v15 w1)) 0
  exact v16
-- Actual MMB 811 addS1
theorem p811 (a0 : M) (a1 : M)  : (t10 (t44 (t29 (a0)) (a1)) (t29 (t44 (a0) (a1)))) := by
  let e0  : M := (t29 (a0))
  let e1 (u0 : M) : Prop := (t10 u0 (a1))
  let e2 (u0 : M) : M := (t44 (a0) u0)
  let e3  : M := (t44 (a0) (a1))
  let e4 (u0 : M) : M := (t44 (e0) u0)
  let e5  : M := (t44 (e0) (a1))
  let e6 (u0 : M) : M := (t29 (e2 u0))
  let e7  : M := (t29 (e3))
  let e8  : M := (t28)
  let e9 (u0 : M) : Prop := (t10 u0 (e8))
  let e10  : M := (t44 (a0) (e8))
  let e11  : M := (t44 (e0) (e8))
  let e12  : M := (t29 (e10))
  let e13 (u0 : M) (u1 : M) : Prop := (t10 u0 u1)
  let e14 (u0 : M) : M := (t44 (a0) u0)
  let e15 (u0 : M) : M := (t44 (e0) u0)
  let e16 (u0 : M) : M := (t29 (e14 u0))
  let e17 (u0 : M) : M := (t29 u0)
  let e18 (u0 : M) (u1 : M) : Prop := (t10 u0 (e17 u1))
  let e19 (u0 : M) : M := (t44 (a0) (e17 u0))
  let e20 (u0 : M) : M := (t44 (e0) (e17 u0))
  let e21 (u0 : M) : M := (t29 (e19 u0))
  let e22  : Prop := (t10 (e11) (e0))
  let e23  : Prop := (t10 (e12) (e0))
  let e24  : Prop := (t10 (e11) (e12))
  let e25  : Prop := (t0 (e23) (e24))
  let e26  : Prop := (t10 (e10) (a0))
  let e27 (u0 : M) : Prop := (t10 (e15 u0) (e16 u0))
  let e28 (u0 : M) : M := (t29 (e15 u0))
  let e29 (u0 : M) : Prop := (t10 (e4 u0) (e6 u0))
  let e30  : Prop := (t10 (e5) (e7))
  let e31 (u0 : M) : Prop := (t10 (e20 u0) (e21 u0))
  let certificate : ZF209.MM0ModelPeano.FormulaCertificate (fun _ : Nat => a0) 1 (fun v => e29 (v 0)) := {
    formula := “x. (&0+1)+x=(&0+x)+1”
    correct := by intro v; simp [e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,e20,e21,e22,e23,e24,e25,e26,e27,e28,e29,e30,e31,t0,t1,t8,t9,t10,t13,t28,t29,t44]
  }
  have v0 := fun z0 : M => p801 (e0) z0 (a1)
  have v1 := fun z0 : M => p801 (a0) z0 (a1)
  have v2 := fun z0 : M => p740 (e1 z0) (e2 z0) (e3) (v1 z0)
  have v3 := fun z0 : M => p350 (e1 z0) (e4 z0) (e5) (e6 z0) (e7) (v0 z0) (v2 z0)
  have v4 := fun z0 : M => p801 (e0) z0 (e8)
  have v5 := fun z0 : M => p801 (a0) z0 (e8)
  have v6 := fun z0 : M => p740 (e9 z0) (e2 z0) (e10) (v5 z0)
  have v7 := fun z0 : M => p350 (e9 z0) (e4 z0) (e11) (e6 z0) (e12) (v4 z0) (v6 z0)
  have v8 := fun z0 : M => fun z1 : M => p801 (e0) z0 z1
  have v9 := fun z0 : M => fun z1 : M => p801 (a0) z0 z1
  have v10 := fun z0 : M => fun z1 : M => p740 (e13 z0 z1) (e2 z0) (e14 z1) (v9 z0 z1)
  have v11 := fun z0 : M => fun z1 : M => p350 (e13 z0 z1) (e4 z0) (e15 z1) (e6 z0) (e16 z1) (v8 z0 z1) (v10 z0 z1)
  have v12 := fun z0 : M => fun z1 : M => p801 (e0) z0 (e17 z1)
  have v13 := fun z0 : M => fun z1 : M => p801 (a0) z0 (e17 z1)
  have v14 := fun z0 : M => fun z1 : M => p740 (e18 z0 z1) (e2 z0) (e19 z1) (v13 z0 z1)
  have v15 := fun z0 : M => fun z1 : M => p350 (e18 z0 z1) (e4 z0) (e20 z1) (e6 z0) (e21 z1) (v12 z0 z1) (v14 z0 z1)
  have v16 := p344 (e11) (e0) (e12)
  have v17 := b792 (e0)
  have v18 := ((v16) (v17))
  have v19 := p739 (e10) (a0)
  have v20 := b792 (a0)
  have v21 := ((v19) (v20))
  have v22 := ((v18) (v21))
  have v23 := fun z0 : M => b793 (e0) z0
  have v24 := fun z0 : M => b793 (a0) z0
  have v25 := fun z0 : M => p8 (e27 z0)
  have v26 := fun z0 : M => p363 (e27 z0) (e15 z0) (e16 z0) (e19 z0) (v24 z0) (v25 z0)
  have v27 := fun z0 : M => p740 (e27 z0) (e15 z0) (e19 z0) (v26 z0)
  have v28 := fun z0 : M => p360 (e27 z0) (e20 z0) (e28 z0) (e21 z0) (v23 z0) (v27 z0)
  have v29 := p741 (fun _ : Nat => a0) (fun w1 : M => (a1)) (fun w0 : M => (e29 w0)) (fun w1 : M => (e24)) (fun w1 : M => (e30)) (fun w1 : M => (e27 w1)) (fun w1 : M => (e31 w1)) certificate ((fun w0 : M => (fun w1 : M => v3 w0))) ((fun w0 : M => (fun w1 : M => v7 w0))) ((fun w0 : M => (fun w1 : M => v11 w0 w1))) ((fun w0 : M => (fun w1 : M => v15 w0 w1))) ((fun w1 : M => v22)) ((fun w1 : M => v28 w1)) 0
  exact v29
-- Actual MMB 812 addSass
theorem p812 (a0 : M) (a1 : M)  : (t10 (t44 (t29 (a0)) (a1)) (t44 (a0) (t29 (a1)))) := by
  have v0 := p344 ((show M from (t44 ((show M from (t29 (a0)))) (a1)))) ((show M from (t29 ((show M from (t44 (a0) (a1))))))) ((show M from (t44 (a0) ((show M from (t29 (a1)))))))
  have v1 := p811 (a0) (a1)
  have v2 := ((v0) (v1))
  have v3 := b793 (a0) (a1)
  have v4 := ((v2) (v3))
  exact v4
-- Actual MMB 813 add12
theorem p813 (a0 : M)  : (t10 (t44 (a0) (t30)) (t29 (a0))) := by
  let e1  : M := (t44 (a0) ((show M from (t30))))
  let e2  : M := (t28)
  let e3  : M := (t44 (a0) (e2))
  let e4  : M := (t29 (e3))
  let e6  : Prop := (t10 (e1) (e4))
  have v0 := p342 (e1) (e4) ((show M from (t29 (a0))))
  have v1 := b793 (a0) (e2)
  have v2 : (e6) := (show (e6) from v1)
  have v3 := ((v0) (v2))
  have v4 := p739 (e3) (a0)
  have v5 := b792 (a0)
  have v6 := ((v4) (v5))
  have v7 := ((v3) (v6))
  exact v7
-- Actual MMB 814 add11
theorem p814 (a0 : M)  : (t10 (t44 (t30) (a0)) (t29 (a0))) := by
  let e1  : M := (t44 ((show M from (t30))) (a0))
  let e2  : M := (t28)
  let e3  : M := (t44 (e2) (a0))
  let e4  : M := (t29 (e3))
  let e6  : Prop := (t10 (e1) (e4))
  have v0 := p342 (e1) (e4) ((show M from (t29 (a0))))
  have v1 := p811 (e2) (a0)
  have v2 : (e6) := (show (e6) from v1)
  have v3 := ((v0) (v2))
  have v4 := p739 (e3) (a0)
  have v5 := p809 (a0)
  have v6 := ((v4) (v5))
  have v7 := ((v3) (v6))
  exact v7
-- Actual MMB 815 add22
end ZF209.MM0ModelReplay
