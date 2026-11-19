module
public import ModelReplay2328
public import ModelRestrictedGraphCertificate
public import ModelLiteralDomainSizeCertificate
public import ModelLiteralSetCodeCertificate
public import ModelNumericSetDefinitions
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2351 lreceqd
theorem p2351 (a0 : Prop) (a1 : M) (a2 : M) (a3 : (M → Prop)) (a4 : (M → Prop)) (a5 : M) (a6 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) (h1 : (t0 (a0) (t17 (M := M) (a3) (a4)))) (h2 : (t0 (a0) (t10 (M := M) (a5) (a6)))) : (t0 (a0) (t10 (M := M) (t142 (a1) (a3) (a5)) (t142 (a2) (a4) (a6)))) := by
  let e0 (u0 : M) : (M → Prop) := (t120 u0)
  let e1 (u0 : M) : (M → Prop) := (t76 (M := M) (e0 u0))
  let e2 (u0 : M) : M := (t125 (e1 u0))
  let e4 (u0 : M) : Prop := (t10 (M := M) u0 ((show M from (t28 (M := M)))))
  let e6 (u0 : M) : M := (t46 (M := M) u0 ((show M from (t30 (M := M)))))
  let e7 (u0 : M) : M := (t64 (M := M) (e6 u0))
  let e8 (u0 : M) : M := (t65 (M := M) (e6 u0))
  let e9 (u0 : M) (u1 : M) : M := (t84 (M := M) (e0 u0) (e8 u1))
  let e10 (u0 : M) (u1 : M) : M := (t63 (M := M) (e8 u1) (e9 u0 u1))
  let e11 (u0 : M) (u1 : M) : M := (t63 (M := M) (e7 u1) (e10 u0 u1))
  let e12 (u0 : M) (u1 : M) : M := (t84 (M := M) (a3) (e11 u0 u1))
  let e13 (u0 : M) (u1 : M) : M := (t84 (M := M) (a4) (e11 u0 u1))
  let e14 (u0 : M) (u1 : M) : M := (t50 (M := M) (e4 u1) (a1) (e12 u0 u1))
  let e15 (u0 : M) (u1 : M) : M := (t50 (M := M) (e4 u1) (a2) (e13 u0 u1))
  let e16 (u0 : M) : M := (t43 (M := M) (e2 u0) (fun x0_1 : M => (e14 u0 x0_1)))
  let e17 (u0 : M) : M := (t43 (M := M) (e2 u0) (fun x0_1 : M => (e15 u0 x0_1)))
  let e23  : Prop := (t0 (a0) ((show Prop from (t10 (M := M) ((show M from (t142 (a1) (a3) (a5)))) ((show M from (t142 (a2) (a4) (a6))))))))
  have v0 := fun z0 : M => p354 (M := M) (a0) (e2 z0)
  have v1 := fun z0 : M => p116 (a0) (e4 z0)
  have v2 := fun z0 : M => fun z1 : M => p1477 (M := M) (a0) (a3) (a4) (e11 z0 z1) (h1)
  have v3 := fun z0 : M => fun z1 : M => p978 (M := M) (a0) (e4 z1) (e4 z1) (a1) (a2) (e12 z0 z1) (e13 z0 z1) (v1 z1) (h0) (v2 z0 z1)
  have v4 := fun z0 : M => p772 (M := M) (a0) (fun w1 : M => (e2 z0)) (fun w1 : M => (e2 z0)) (fun w1 : M => (e14 z0 w1)) (fun w1 : M => (e15 z0 w1)) ((fun w1 : M => v0 z0)) ((fun w1 : M => v3 z0 w1)) 0
  have v5 := p1436 (M := M) (a0) (fun w1 : M => (e16 w1)) (fun w1 : M => (e17 w1)) ((fun w1 : M => v4 w1))
  have v6 := p2316 (M := M) (a0) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (e16 x0_0))))) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (e17 x0_0))))) (a5) (a6) (v5) (h2)
  have v7 : (e23) := (show (e23) from v6)
  exact v7
-- Actual MMB 2352 lreceq
theorem p2357 (a0 : Prop) (a1 : M) (a2 : (M → Prop)) (a3 : M) (a4 : M) (h0 : (t0 (a0) (t10 (M := M) (a3) (a4)))) : (t0 (a0) (t10 (M := M) (t142 (a1) (a2) (a3)) (t142 (a1) (a2) (a4)))) := by
  have v0 := p354 (M := M) (a0) (a1)
  have v1 := p562 (M := M) (a0) (a2)
  have v2 := p2351 (M := M) (a0) (a1) (a1) (a2) (a2) (a3) (a4) (v0) (v1) (h0)
  exact v2
-- Actual MMB 2358 lreceq3
theorem p2358 (a0 : M) (a1 : (M → Prop)) (a2 : M) (a3 : M)  : (t0 (t10 (M := M) (a2) (a3)) (t10 (M := M) (t142 (a0) (a1) (a2)) (t142 (a0) (a1) (a3)))) := by
  let e0  : Prop := (t10 (M := M) (a2) (a3))
  have v0 := p8 (e0)
  have v1 := p2357 (M := M) (e0) (a0) (a1) (a2) (a3) (v0)
  exact v1

end ZF207.MM0ModelReplay
