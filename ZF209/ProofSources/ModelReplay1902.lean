module
public import ModelReplay1894
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 1895 receqd
theorem p1895 (a0 : Prop) (a1 : M) (a2 : M) (a3 : (M → Prop)) (a4 : (M → Prop)) (a5 : M) (a6 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) (h1 : (t0 (a0) (t17 (M := M) (a3) (a4)))) (h2 : (t0 (a0) (t10 (M := M) (a5) (a6)))) : (t0 (a0) (t10 (M := M) (t110 (M := M) (a1) (a3) (a5)) (t110 (M := M) (a2) (a4) (a6)))) := by
  let e0 (u0 : M) : (M → Prop) := (t109 (M := M) u0)
  let e2 (u0 : M) : M := (t84 (M := M) (e0 u0) ((show M from (t28 (M := M)))))
  let e3 (u0 : M) : M := (t84 (M := M) (e0 u0) (a5))
  let e4 (u0 : M) : M := (t84 (M := M) (e0 u0) (a6))
  let e5 (u0 : M) : Prop := (t10 (M := M) (e2 u0) (a1))
  let e6 (u0 : M) : Prop := (t10 (M := M) (e2 u0) (a2))
  let e7 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e3 u0) u1)
  let e8 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e4 u0) u1)
  let e9 (u0 : M) (u1 : M) : M := (t84 (M := M) (e0 u0) u1)
  let e10 (u0 : M) : M := (t29 (M := M) u0)
  let e11 (u0 : M) (u1 : M) : M := (t84 (M := M) (e0 u0) (e10 u1))
  let e12 (u0 : M) (u1 : M) : M := (t84 (M := M) (a3) (e9 u0 u1))
  let e13 (u0 : M) (u1 : M) : M := (t84 (M := M) (a4) (e9 u0 u1))
  let e14 (u0 : M) : Prop := (t48 (M := M) u0 (a5))
  let e15 (u0 : M) : Prop := (t48 (M := M) u0 (a6))
  let e16 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e11 u0 u1) (e12 u0 u1))
  let e17 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e11 u0 u1) (e13 u0 u1))
  let e18 (u0 : M) (u1 : M) : Prop := (t0 (e14 u1) (e16 u0 u1))
  let e19 (u0 : M) (u1 : M) : Prop := (t0 (e15 u1) (e17 u0 u1))
  let e20 (u0 : M) (u1 : M) : Prop := (t2 (e5 u0) (e7 u0 u1))
  let e21 (u0 : M) (u1 : M) : Prop := (t2 (e6 u0) (e8 u0 u1))
  let e22 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e18 u0 x0_0)))
  let e23 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e19 u0 x0_0)))
  let e24 (u0 : M) (u1 : M) : Prop := (t2 (e20 u0 u1) (e22 u0))
  let e25 (u0 : M) (u1 : M) : Prop := (t2 (e21 u0 u1) (e23 u0))
  let e26 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (e24 x0_0 u0)))
  let e27 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (e25 x0_0 u0)))
  let e33  : Prop := (t0 (a0) ((show Prop from (t10 (M := M) ((show M from (t110 (M := M) (a1) (a3) (a5)))) ((show M from (t110 (M := M) (a2) (a4) (a6))))))))
  have v0 := fun z0 : M => p349 (M := M) (a0) (e2 z0) (a1) (a2) (h0)
  have v1 := fun z0 : M => p1479 (M := M) (a0) (e0 z0) (a5) (a6) (h2)
  have v2 := fun z0 : M => fun z1 : M => p348 (M := M) (a0) (e3 z0) (e4 z0) z1 (v1 z0)
  have v3 := fun z0 : M => fun z1 : M => p196 (a0) (e5 z0) (e6 z0) (e7 z0 z1) (e8 z0 z1) (v0 z0) (v2 z0 z1)
  have v4 := fun z0 : M => p890 (M := M) (a0) z0 (a5) (a6) (h2)
  have v5 := fun z0 : M => fun z1 : M => p1477 (M := M) (a0) (a3) (a4) (e9 z0 z1) (h1)
  have v6 := fun z0 : M => fun z1 : M => p349 (M := M) (a0) (e11 z0 z1) (e12 z0 z1) (e13 z0 z1) (v5 z0 z1)
  have v7 := fun z0 : M => fun z1 : M => p188 (a0) (e14 z1) (e15 z1) (e16 z0 z1) (e17 z0 z1) (v4 z1) (v6 z0 z1)
  have v8 := fun z0 : M => p371 (M := M) (a0) (fun w1 : M => (e18 z0 w1)) (fun w1 : M => (e19 z0 w1)) ((fun w1 : M => v7 z0 w1))
  have v9 := fun z0 : M => fun z1 : M => p196 (a0) (e20 z0 z1) (e21 z0 z1) (e22 z0) (e23 z0) (v3 z0 z1) (v8 z0)
  have v10 := fun z0 : M => p379 (M := M) (a0) (fun w1 : M => (e24 w1 z0)) (fun w1 : M => (e25 w1 z0)) ((fun w1 : M => v9 w1 z0))
  have v11 := p584 (M := M) (a0) (fun w1 : M => (e26 w1)) (fun w1 : M => (e27 w1)) ((fun w1 : M => v10 w1))
  have v12 := p748 (M := M) (a0) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e26 x0_0))))) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e27 x0_0))))) (v11)
  have v13 : (e33) := (show (e33) from v12)
  exact v13
-- Actual MMB 1896 receq
theorem p1901 (a0 : Prop) (a1 : M) (a2 : (M → Prop)) (a3 : M) (a4 : M) (h0 : (t0 (a0) (t10 (M := M) (a3) (a4)))) : (t0 (a0) (t10 (M := M) (t110 (M := M) (a1) (a2) (a3)) (t110 (M := M) (a1) (a2) (a4)))) := by
  have v0 := p354 (M := M) (a0) (a1)
  have v1 := p562 (M := M) (a0) (a2)
  have v2 := p1895 (M := M) (a0) (a1) (a1) (a2) (a2) (a3) (a4) (v0) (v1) (h0)
  exact v2
-- Actual MMB 1902 receq3
theorem p1902 (a0 : M) (a1 : (M → Prop)) (a2 : M) (a3 : M)  : (t0 (t10 (M := M) (a2) (a3)) (t10 (M := M) (t110 (M := M) (a0) (a1) (a2)) (t110 (M := M) (a0) (a1) (a3)))) := by
  let e0  : Prop := (t10 (M := M) (a2) (a3))
  have v0 := p8 (e0)
  have v1 := p1901 (M := M) (e0) (a0) (a1) (a2) (a3) (v0)
  exact v1

end ZF209.MM0ModelReplay
