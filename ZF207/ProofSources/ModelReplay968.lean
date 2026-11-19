module
public import ModelReplay966
public import ModelReplayCertificateHelpers
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 967 indlt
theorem p967 (e : Nat → M) (a0 : Prop) (a3 : M) (a4 : M → Prop) (a5 : M → Prop) (a6 : M → Prop) (a7 : M → Prop) (a8 : M → Prop) (c0 : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun _ => a0)) (c4 : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => a4 (v 0))) (h0 : (∀ z0 : M, (∀ z1 : M, (t0 (t10 z0 (a3)) (t3 (a4 z0) (a6 z1)))))) (h1 : (∀ z0 : M, (∀ z1 : M, (t0 (t10 z0 (t28)) (t3 (a4 z0) (a5 z1)))))) (h2 : (∀ z0 : M, (∀ z1 : M, (t0 (t10 z0 z1) (t3 (a4 z0) (a7 z1)))))) (h3 : (∀ z0 : M, (∀ z1 : M, (t0 (t10 z0 (t29 z1)) (t3 (a4 z0) (a8 z1)))))) (h4 : (∀ z0 : M, (t0 (a0) (a5 z0)))) (h5 : (∀ z0 : M, (t0 (t2 (t2 (a0) (t48 z0 (a3))) (a7 z0)) (a8 z0)))) : (∀ z0 : M, (t0 (a0) (a6 z0))) := by
  let e0 (u0 : M) : Prop := (t10 u0 (a3))
  let e1 (u0 : M) : Prop := (t47 u0 (a3))
  let e2  : Prop := (t47 (a3) (a3))
  let e3  : M := (t28)
  let e4 (u0 : M) : Prop := (t10 u0 (e3))
  let e5  : Prop := (t47 (e3) (a3))
  let e6 (u0 : M) (u1 : M) : Prop := (t10 u0 u1)
  let e7 (u0 : M) : Prop := (t47 u0 (a3))
  let e8 (u0 : M) : M := (t29 u0)
  let e9 (u0 : M) (u1 : M) : Prop := (t10 u0 (e8 u1))
  let e10 (u0 : M) : Prop := (t47 (e8 u0) (a3))
  let e11 (u0 : M) : Prop := (t48 u0 (a3))
  let e12 (u0 : M) : Prop := (t2 (a0) (e11 u0))
  let e13 (u0 : M) : Prop := (t0 (a7 u0) (a8 u0))
  let e14 (u0 : M) : Prop := (t0 (e11 u0) (a7 u0))
  let e15 (u0 : M) : Prop := (t0 (e10 u0) (a8 u0))
  let e16 (u0 : M) : Prop := (t0 (e14 u0) (e15 u0))
  let e17 (u0 : M) : Prop := (t0 (a0) (e16 u0))
  let e18 (u0 : M) : Prop := (t0 (e7 u0) (a7 u0))
  let e19 (u0 : M) : Prop := (t0 (e1 u0) (a4 u0))
  let e20 (u0 : M) : Prop := (t0 (e5) (a5 u0))
  let e21 (u0 : M) : Prop := (t0 (e2) (a6 u0))
  let ee : Nat → M := fun i => Nat.casesOn i a3 e
  let cb : ZF207.MM0ModelPeano.FormulaCertificate ee 1 (fun v => e1 (v 0)) := {
    formula := “x. ∃ q, x+q=&0”
    correct := by
      intro v
      classical
      simp [e1,t47,t9,t1,t8,t10,t44,ee]
  }
  let certificate := cb.imp (c4.prependParameter a3)
  have v0 := p857 (a3)
  have v1 := fun z0 : M => p853 z0 (a3) (a3)
  have v2 := fun z0 : M => fun z1 : M => p188 (e0 z0) (e1 z0) (e2) (a4 z0) (a6 z1) (v1 z0) (h0 z0 z1)
  have v3 := fun z0 : M => p853 z0 (e3) (a3)
  have v4 := fun z0 : M => fun z1 : M => p188 (e4 z0) (e1 z0) (e5) (a4 z0) (a5 z1) (v3 z0) (h1 z0 z1)
  have v5 := fun z0 : M => fun z1 : M => p853 z0 z1 (a3)
  have v6 := fun z0 : M => fun z1 : M => p188 (e6 z0 z1) (e1 z0) (e7 z1) (a4 z0) (a7 z1) (v5 z0 z1) (h2 z0 z1)
  have v7 := fun z0 : M => fun z1 : M => p853 z0 (e8 z1) (a3)
  have v8 := fun z0 : M => fun z1 : M => p188 (e9 z0 z1) (e1 z0) (e10 z1) (a4 z0) (a8 z1) (v7 z0 z1) (h3 z0 z1)
  have v9 := fun z0 : M => p12 (a0) (a5 z0) (e5) (h4 z0)
  have v10 := fun z0 : M => p894 z0 (a3)
  have v11 := fun z0 : M => p29 (e11 z0) (e7 z0) (a7 z0) (v10 z0)
  have v12 := fun z0 : M => p84 (e12 z0) (a7 z0) (a8 z0) (h5 z0)
  have v13 := fun z0 : M => p84 (a0) (e11 z0) (e13 z0) (v12 z0)
  have v14 := fun z0 : M => p13 (a0) (e11 z0) (a7 z0) (a8 z0) (v13 z0)
  have v15 : (∀ z0 : M, (e17 z0)) := (show (∀ z0 : M, (e17 z0)) from v14)
  have v16 := fun z0 : M => p17 (a0) (e18 z0) (e14 z0) (e15 z0) (v11 z0) (v15 z0)
  have v17 := fun z0 : M => p83 (a0) (e18 z0) (e15 z0) (v16 z0)
  have v18 := fun z0 : M => p742 ee (a0) (fun w2 : M => (a3)) (fun w1 : M => (e19 w1)) (fun w2 : M => (e20 w2)) (fun w2 : M => (e21 w2)) (fun w2 : M => (e18 w2)) (fun w2 : M => (e15 w2)) (c0.prependParameter a3) certificate ((fun w1 : M => (fun w2 : M => v2 w1 w2))) ((fun w1 : M => (fun w2 : M => v4 w1 w2))) ((fun w1 : M => (fun w2 : M => v6 w1 w2))) ((fun w1 : M => (fun w2 : M => v8 w1 w2))) ((fun w2 : M => v9 w2)) ((fun w2 : M => v17 w2)) z0
  have v19 := fun z0 : M => p7 (a0) (e2) (a6 z0) (v0) (v18 z0)
  exact v19
-- Actual MMB 968 indstr
theorem p968 (e : Nat → M) (a0 : Prop) (a3 : M → M) (a4 : M → Prop) (a5 : M → Prop) (a6 : M → Prop) (c0 : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun _ => a0)) (c4 : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => a4 (v 0))) (h0 : (∀ z0 : M, (∀ z1 : M, (t0 (t10 z0 (a3 z1)) (t3 (a4 z0) (a5 z1)))))) (h1 : (∀ z0 : M, (∀ z1 : M, (t0 (t10 z0 z1) (t3 (a4 z0) (a6 z1)))))) (h2 : (∀ z0 : M, (t0 (t2 (a0) (t8 (fun x2_0 : M => (t0 (t48 x2_0 z0) (a4 x2_0))))) (a6 z0)))) : (∀ z0 : M, (t0 (a0) (a5 z0))) := by
  let e0 (u0 : M) : M := (t29 (a3 u0))
  let e1 (u0 : M) (u1 : M) : Prop := (t10 u0 (a3 u1))
  let e2 (u0 : M) (u1 : M) : Prop := (t48 u0 (e0 u1))
  let e3 (u0 : M) : Prop := (t48 (a3 u0) (e0 u0))
  let e4 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0 u1) (a4 u0))
  let e5 (u0 : M) : Prop := (t0 (e3 u0) (a5 u0))
  let e6 (u0 : M) : Prop := (t8 (fun x0_0 : M => (e4 x0_0 u0)))
  let e7 (u0 : M) (u1 : M) : Prop := (t10 u0 (e0 u1))
  let e8 (u0 : M) (u1 : M) : Prop := (t48 u1 u0)
  let e9 (u0 : M) (u1 : M) : Prop := (t0 (e8 u0 u1) (a4 u1))
  let e10  : M := (t28)
  let e11 (u0 : M) : Prop := (t10 u0 (e10))
  let e12 (u0 : M) : Prop := (t48 u0 (e10))
  let e13 (u0 : M) : Prop := (t0 (e12 u0) (a4 u0))
  let e14 (u0 : M) (u1 : M) : Prop := (t10 u0 u1)
  let e15 (u0 : M) (u1 : M) : Prop := (t48 u0 u1)
  let e16 (u0 : M) (u1 : M) : Prop := (t0 (e15 u0 u1) (a4 u0))
  let e17 (u0 : M) : M := (t29 u0)
  let e18 (u0 : M) (u1 : M) : Prop := (t10 u0 (e17 u1))
  let e19 (u0 : M) (u1 : M) : Prop := (t48 u0 (e17 u1))
  let e20 (u0 : M) (u1 : M) : Prop := (t0 (e19 u0 u1) (a4 u0))
  let e21 (u0 : M) : Prop := (t1 (e12 u0))
  let e22  : Prop := (t8 (fun x0_0 : M => (e13 x0_0)))
  let e23 (u0 : M) (u1 : M) : Prop := (t10 u0 u1)
  let e24 (u0 : M) (u1 : M) : Prop := (t0 (e23 u0 u1) (a4 u0))
  let e25 (u0 : M) : Prop := (t8 (fun x0_0 : M => (e16 x0_0 u0)))
  let e26 (u0 : M) : Prop := (t2 (a0) (e25 u0))
  let e27 (u0 : M) : Prop := (t8 (fun x0_0 : M => (e24 x0_0 u0)))
  let e28 (u0 : M) (u1 : M) : Prop := (t47 u0 u1)
  let e29 (u0 : M) (u1 : M) : Prop := (t4 (e15 u0 u1) (e23 u0 u1))
  let e30 (u0 : M) (u1 : M) : Prop := (t3 (e28 u0 u1) (e19 u0 u1))
  let e31 (u0 : M) (u1 : M) : Prop := (t3 (e28 u0 u1) (e29 u0 u1))
  let e32 (u0 : M) (u1 : M) : Prop := (t3 (e19 u0 u1) (e29 u0 u1))
  let e33 (u0 : M) (u1 : M) : Prop := (t0 (e31 u0 u1) (e32 u0 u1))
  let e34 (u0 : M) (u1 : M) : Prop := (t0 (e29 u0 u1) (a4 u0))
  let e35 (u0 : M) : Prop := (t8 (fun x0_0 : M => (e20 x0_0 u0)))
  let e36 (u0 : M) : Prop := (t0 (e27 u0) (e35 u0))
  let e37 (u0 : M) : Prop := (t8 (fun x0_0 : M => (e9 u0 x0_0)))
  let certificate : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => e37 (v 0)) := {
    formula := c4.boundedAll.formula
    correct := by
      intro v
      classical
      simpa [e37,e9,e8,t0,t48,t47,t9,t1,t8,t10,t44,t29] using c4.boundedAll.correct v
  }
  have v0 := fun z0 : M => p902 (a3 z0)
  have v1 := fun z0 : M => fun z1 : M => p889 z0 (a3 z1) (e0 z1)
  have v2 := fun z0 : M => fun z1 : M => p188 (e1 z0 z1) (e2 z0 z1) (e3 z1) (a4 z0) (a5 z1) (v1 z0 z1) (h0 z0 z1)
  have v3 := fun z0 : M => p440 (a3 z0) (fun w0 : M => (e4 w0 z0)) (e5 z0) ((fun w0 : M => v2 w0 z0))
  have v4 := fun z0 : M => p7 (e6 z0) (e3 z0) (a5 z0) (v0 z0) (v3 z0)
  have v5 := fun z0 : M => fun z1 : M => p8 (e7 z0 z1)
  have v6 := fun z0 : M => fun z1 : M => fun z2 : M => p890 (e7 z0 z2) z1 z0 (e0 z2) (v5 z0 z2)
  have v7 := fun z0 : M => fun z1 : M => fun z2 : M => p191 (e7 z0 z2) (e8 z0 z1) (e2 z1 z2) (a4 z1) (v6 z0 z1 z2)
  have v8 := fun z0 : M => fun z1 : M => p371 (e7 z0 z1) (fun w1 : M => (e9 z0 w1)) (fun w1 : M => (e4 w1 z1)) ((fun w1 : M => v7 z0 w1 z1))
  have v9 := fun z0 : M => p8 (e11 z0)
  have v10 := fun z0 : M => fun z1 : M => p890 (e11 z0) z1 z0 (e10) (v9 z0)
  have v11 := fun z0 : M => fun z1 : M => p191 (e11 z0) (e8 z0 z1) (e12 z1) (a4 z1) (v10 z0 z1)
  have v12 := fun z0 : M => p371 (e11 z0) (fun w1 : M => (e9 z0 w1)) (fun w1 : M => (e13 w1)) ((fun w1 : M => v11 z0 w1))
  have v13 := fun z0 : M => fun z1 : M => p8 (e14 z0 z1)
  have v14 := fun z0 : M => fun z1 : M => fun z2 : M => p890 (e14 z0 z2) z1 z0 z2 (v13 z0 z2)
  have v15 := fun z0 : M => fun z1 : M => fun z2 : M => p191 (e14 z0 z2) (e8 z0 z1) (e15 z1 z2) (a4 z1) (v14 z0 z1 z2)
  have v16 := fun z0 : M => fun z1 : M => p371 (e14 z0 z1) (fun w1 : M => (e9 z0 w1)) (fun w1 : M => (e16 w1 z1)) ((fun w1 : M => v15 z0 w1 z1))
  have v17 := fun z0 : M => fun z1 : M => p8 (e18 z0 z1)
  have v18 := fun z0 : M => fun z1 : M => fun z2 : M => p890 (e18 z0 z2) z1 z0 (e17 z2) (v17 z0 z2)
  have v19 := fun z0 : M => fun z1 : M => fun z2 : M => p191 (e18 z0 z2) (e8 z0 z1) (e19 z1 z2) (a4 z1) (v18 z0 z1 z2)
  have v20 := fun z0 : M => fun z1 : M => p371 (e18 z0 z1) (fun w1 : M => (e9 z0 w1)) (fun w1 : M => (e20 w1 z1)) ((fun w1 : M => v19 z0 w1 z1))
  have v21 := fun z0 : M => p22 (e12 z0) (a4 z0)
  have v22 := fun z0 : M => p904 z0
  have v23 := fun z0 : M => b3 (e21 z0) (e13 z0) (v21 z0) (v22 z0)
  have v24 := b325 (fun w0 : M => (e13 w0)) ((fun w0 : M => v23 w0))
  have v25 := p4 (a0) (e22) (v24)
  have v26 := fun z0 : M => fun z1 : M => p110 (e23 z0 z1) (a4 z0) (a6 z1) (h1 z0 z1)
  have v27 := fun z0 : M => fun z1 : M => p23 (e23 z0 z1) (a6 z1) (a4 z0) (v26 z0 z1)
  have v28 := fun z0 : M => p338 (a6 z0) (fun w0 : M => (e24 w0 z0)) ((fun w0 : M => v27 w0 z0))
  have v29 := fun z0 : M => p11 (e26 z0) (a6 z0) (e27 z0) (h2 z0) (v28 z0)
  have v30 := fun z0 : M => fun z1 : M => p151 (e19 z0 z1) (e28 z0 z1) (e29 z0 z1)
  have v31 := fun z0 : M => fun z1 : M => p910 z0 z1
  have v32 := fun z0 : M => fun z1 : M => b3 (e30 z0 z1) (e33 z0 z1) (v30 z0 z1) (v31 z0 z1)
  have v33 := fun z0 : M => fun z1 : M => p926 z0 z1
  have v34 := fun z0 : M => fun z1 : M => b3 (e31 z0 z1) (e32 z0 z1) (v32 z0 z1) (v33 z0 z1)
  have v35 := fun z0 : M => fun z1 : M => p105 (e19 z0 z1) (e29 z0 z1) (v34 z0 z1)
  have v36 := fun z0 : M => fun z1 : M => p29 (e19 z0 z1) (e29 z0 z1) (a4 z0) (v35 z0 z1)
  have v37 := fun z0 : M => fun z1 : M => p256 (e15 z0 z1) (e23 z0 z1) (a4 z0)
  have v38 := fun z0 : M => fun z1 : M => p18 (e16 z0 z1) (e24 z0 z1) (e34 z0 z1) (e20 z0 z1) (v36 z0 z1) (v37 z0 z1)
  have v39 := fun z0 : M => p370 (fun w0 : M => (e16 w0 z0)) (fun w0 : M => (e24 w0 z0)) (fun w0 : M => (e20 w0 z0)) ((fun w0 : M => v38 w0 z0))
  have v40 := fun z0 : M => p63 (a0) (e25 z0) (e36 z0) (v39 z0)
  have v41 := fun z0 : M => p6 (e26 z0) (e27 z0) (e35 z0) (v29 z0) (v40 z0)
  have v42 := fun z0 : M => p742 e (a0) (fun w2 : M => (e0 w2)) (fun w1 : M => (e37 w1)) (fun w2 : M => (e22)) (fun w2 : M => (e6 w2)) (fun w2 : M => (e25 w2)) (fun w2 : M => (e35 w2)) c0 certificate ((fun w1 : M => (fun w2 : M => v8 w1 w2))) ((fun w1 : M => (fun w2 : M => v12 w1))) ((fun w1 : M => (fun w2 : M => v16 w1 w2))) ((fun w1 : M => (fun w2 : M => v20 w1 w2))) ((fun w2 : M => v25)) ((fun w2 : M => v41 w2)) z0
  have v43 := fun z0 : M => p10 (a0) (e6 z0) (a5 z0) (v4 z0) (v42 z0)
  exact v43

end ZF207.MM0ModelReplay
