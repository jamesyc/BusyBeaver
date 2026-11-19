module
public import ModelReplay741
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 742 indd
theorem p742 (e : Nat → M) (a0 : Prop) (a3 : M → M) (a4 : M → Prop) (a5 : M → Prop) (a6 : M → Prop) (a7 : M → Prop) (a8 : M → Prop) (c0 : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun _ => a0)) (c4 : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => a4 (v 0))) (h0 : (∀ z0 : M, (∀ z1 : M, (t0 (t10 z0 (a3 z1)) (t3 (a4 z0) (a6 z1)))))) (h1 : (∀ z0 : M, (∀ z1 : M, (t0 (t10 z0 (t28)) (t3 (a4 z0) (a5 z1)))))) (h2 : (∀ z0 : M, (∀ z1 : M, (t0 (t10 z0 z1) (t3 (a4 z0) (a7 z1)))))) (h3 : (∀ z0 : M, (∀ z1 : M, (t0 (t10 z0 (t29 z1)) (t3 (a4 z0) (a8 z1)))))) (h4 : (∀ z0 : M, (t0 (a0) (a5 z0)))) (h5 : (∀ z0 : M, (t0 (t2 (a0) (a7 z0)) (a8 z0)))) : (∀ z0 : M, (t0 (a0) (a6 z0))) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 u0 (a3 u1))
  let e2 (u0 : M) : Prop := (t10 u0 ((show M from (t28))))
  let e3 (u0 : M) (u1 : M) : Prop := (t10 u0 u1)
  let e4 (u0 : M) : M := (t29 u0)
  let e5 (u0 : M) (u1 : M) : Prop := (t10 u0 (e4 u1))
  let e6 (u0 : M) : Prop := (t0 (a0) (a4 u0))
  let e7 (u0 : M) : Prop := (t0 (a0) (a5 u0))
  let e8 (u0 : M) : Prop := (t0 (a0) (a6 u0))
  let e9 (u0 : M) : Prop := (t0 (a0) (a7 u0))
  let e10 (u0 : M) : Prop := (t0 (a0) (a8 u0))
  have v0 := fun z0 : M => fun z1 : M => p192 (e0 z0 z1) (a0) (a4 z0) (a6 z1) (h0 z0 z1)
  have v1 := fun z0 : M => fun z1 : M => p192 (e2 z0) (a0) (a4 z0) (a5 z1) (h1 z0 z1)
  have v2 := fun z0 : M => fun z1 : M => p192 (e3 z0 z1) (a0) (a4 z0) (a7 z1) (h2 z0 z1)
  have v3 := fun z0 : M => fun z1 : M => p192 (e5 z0 z1) (a0) (a4 z0) (a8 z1) (h3 z0 z1)
  have v4 := fun z0 : M => p84 (a0) (a7 z0) (a8 z0) (h5 z0)
  have v5 := fun z0 : M => p5 (a0) (a7 z0) (a8 z0) (v4 z0)
  have v6 := fun z0 : M => p741 e (fun w1 : M => (a3 w1)) (fun w0 : M => (e6 w0)) (fun w1 : M => (e7 w1)) (fun w1 : M => (e8 w1)) (fun w1 : M => (e9 w1)) (fun w1 : M => (e10 w1)) (c0.imp c4) ((fun w0 : M => (fun w1 : M => v0 w0 w1))) ((fun w0 : M => (fun w1 : M => v1 w0 w1))) ((fun w0 : M => (fun w1 : M => v2 w0 w1))) ((fun w0 : M => (fun w1 : M => v3 w0 w1))) ((fun w1 : M => h4 w1)) ((fun w1 : M => v5 w1)) z0
  exact v6

end ZF207.MM0ModelReplay
