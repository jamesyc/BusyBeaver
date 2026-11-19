module
public import ModelReplay1903
public import ModelPsetFunctionEqualityCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 1904 rec0
theorem p1904 (a0 : M) (a1 : (M → Prop))  : (t10 (M := M) (t110 (M := M) (a0) (a1) (t28 (M := M))) (a0)) := by
  let e0  : M := (t28 (M := M))
  let e1 (u0 : M) : (M → Prop) := (t109 (M := M) u0)
  let e2 (u0 : M) : Prop := (t10 (M := M) u0 (e0))
  let e3 (u0 : M) (u1 : M) : M := (t84 (M := M) (e1 u1) u0)
  let e4 (u0 : M) : M := (t84 (M := M) (e1 u0) (e0))
  let e5  : Prop := (t10 (M := M) (e0) (e0))
  let e6 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e3 u0 u1) (a0))
  let e7 (u0 : M) : Prop := (t10 (M := M) (e4 u0) (a0))
  let e8 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0) (e6 u0 u1))
  let e9 (u0 : M) : Prop := (t0 (e5) (e7 u0))
  let e10 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e8 x0_0 u0)))
  let e11 (u0 : M) : Prop := (t48 (M := M) u0 (e0))
  let e12 (u0 : M) : M := (t29 (M := M) u0)
  let e13 (u0 : M) (u1 : M) : M := (t84 (M := M) (e1 u0) (e12 u1))
  let e14 (u0 : M) (u1 : M) : M := (t84 (M := M) (e1 u0) u1)
  let e15 (u0 : M) (u1 : M) : M := (t84 (M := M) (a1) (e14 u0 u1))
  let e16 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e13 u0 u1) (e15 u0 u1))
  let e17 (u0 : M) : Prop := (t1 (e11 u0))
  let e18 (u0 : M) (u1 : M) : Prop := (t0 (e11 u1) (e16 u0 u1))
  let e19 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e18 u0 x0_0)))
  let e21  : Prop := (t10 (M := M) ((show M from (t110 (M := M) (a0) (a1) (e0)))) (a0))
  let e24  : Prop := (t9 (M := M) (fun x0_0 : M => (e10 x0_0)))
  let ee : Nat → M := fun _ => a0
  let domainCertificate : ZF207.MM0ModelPeano.FormulaCertificate ee 1 (fun v => e2 (v 0)) := {
    formula := “x. x=0”
    correct := by intro v; rfl
  }
  let functionCertificate : ZF207.MM0ModelPeano.FunctionGraphCertificate ee 1 (fun _ => a0) := {
    formula := “y x. y=&0”
    correct := by intro v y; rfl
  }
  have v0 := p340 (M := M) (e0)
  have v1 := fun z0 : M => p346 (M := M) z0 (e0) (e0)
  have v2 := fun z0 : M => fun z1 : M => p1480 (M := M) (e1 z1) z0 (e0)
  have v3 := fun z0 : M => fun z1 : M => p348 (M := M) (e2 z0) (e3 z0 z1) (e4 z1) (a0) (v2 z0 z1)
  have v4 := fun z0 : M => fun z1 : M => p188 (e2 z0) (e2 z0) (e5) (e6 z0 z1) (e7 z1) (v1 z0) (v3 z0 z1)
  have v5 := fun z0 : M => p440 (M := M) (e0) (fun w0 : M => (e8 w0 z0)) (e9 z0) ((fun w0 : M => v4 w0 z0))
  have v6 := fun z0 : M => p7 (e10 z0) (e5) (e7 z0) (v0) (v5 z0)
  have v7 := fun z0 : M => fun z1 : M => p22 (e11 z1) (e16 z0 z1)
  have v8 := fun z0 : M => p904 (M := M) z0
  have v9 := fun z0 : M => fun z1 : M => b3 (e17 z1) (e18 z0 z1) (v7 z0 z1) (v8 z1)
  have v10 := fun z0 : M => b325 (M := M) (fun w0 : M => (e18 z0 w0)) ((fun w0 : M => v9 z0 w0))
  have v11 := fun z0 : M => p4 (e10 z0) (e19 z0) (v10 z0)
  have v12 := fun z0 : M => p1903 (M := M) (e10 z0) (a1) z0 (e0) (a0) (a0) (v6 z0) (v6 z0) (v11 z0)
  have v13 := p339 (M := M) (fun w0 : M => (e10 w0)) (e21) ((fun w0 : M => v12 w0))
  have v14 := p1894 (M := M) ee (fun w1 : M => (e2 w1)) (fun w1 : M => (a0)) domainCertificate functionCertificate
  have v15 := p975 (M := M) (e0)
  have v16 := b3 ((show Prop from (t49 (M := M) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e2 x0_0)))))))) (e24) (v14) (v15)
  have v17 := b3 (e24) (e21) (v13) (v16)
  exact v17

end ZF207.MM0ModelReplay
