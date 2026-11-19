module
public import ModelReplay2361
public import ModelLiteralContextCodeCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2364 lmemseqd
theorem p2366   : (t10 (M := M) (t143 (t28 (M := M))) (t28 (M := M))) := by
  let e0  : M := (t28 (M := M))
  let e1 (u0 : M) (u1 : M) : M := (t123 u0 u1)
  let e2 (u0 : M) : (M → Prop) := (t82 (M := M) (fun x0_0 : M => (e1 u0 x0_0)))
  let e3 (u0 : M) : (M → Prop) := (t89 (M := M) (fun x0_0 : M => (e2 u0)))
  let e6  : Prop := (t10 (M := M) ((show M from (t143 (e0)))) (e0))
  have v0 := p2360 (M := M) (fun _=>0) (e0) ((show (M → Prop) from (t89 (M := M) (fun x0_0 : M => (e3 x0_0))))) (literalContextBuildStep_certificate (fun _=>0))
  have v1 : (e6) := (show (e6) from v0)
  exact v1
-- Actual MMB 2367 lmemsS
theorem p2367 (a0 : M) (a1 : M)  : (t10 (M := M) (t143 (t131 (a0) (a1))) (t123 (a0) (t143 (a1)))) := by
  let e1  : M := (t143 ((show M from (t131 (a0) (a1)))))
  let e2 (u0 : M) (u1 : M) : M := (t123 u0 u1)
  let e3 (u0 : M) : (M → Prop) := (t82 (M := M) (fun x0_0 : M => (e2 u0 x0_0)))
  let e4 (u0 : M) : (M → Prop) := (t89 (M := M) (fun x0_0 : M => (e3 u0)))
  let e5  : (M → Prop) := (t89 (M := M) (fun x0_0 : M => (e4 x0_0)))
  let e6  : M := (t28 (M := M))
  let e10  : M := (t84 (M := M) (e5) ((show M from (t63 (M := M) (a0) ((show M from (t63 (M := M) (a1) ((show M from (t142 (e6) (e5) (a1)))))))))))
  let e11  : M := (t143 (a1))
  let e12  : M := (t123 (a0) (e11))
  let e13  : Prop := (t10 (M := M) (e1) (e10))
  let e14  : Prop := (t10 (M := M) (e10) (e12))
  let e17 (u0 : M) : Prop := (t10 (M := M) u0 (a0))
  let e18 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e19 (u0 : M) : Prop := (t10 (M := M) u0 (e11))
  let e20 (u0 : M) (u1 : M) : Prop := (t2 (e17 u0) (e18 u1))
  let e21 (u0 : M) (u1 : M) (u2 : M) : Prop := (t2 (e20 u0 u1) (e19 u2))
  have v0 := p342 (M := M) (e1) (e10) (e12)
  have v1 := p2361 (M := M) (fun _=>0) (e6) (e5) (a0) (a1) (literalContextBuildStep_certificate (fun _=>0))
  have v2 : (e13) := (show (e13) from v1)
  have v3 := ((v0) (v2))
  have v4 := fun z0 : M => fun z1 : M => fun z2 : M => p64 (e17 z0) (e18 z1) (e19 z2)
  have v5 := fun z0 : M => fun z1 : M => fun z2 : M => p54 (e20 z0 z1) (e19 z2)
  have v6 := fun z0 : M => fun z1 : M => fun z2 : M => p2115 (M := M) (e21 z0 z1 z2) z0 (a0) z2 (e11) (v4 z0 z1 z2) (v5 z0 z1 z2)
  have v7 := fun z0 : M => fun z1 : M => p1495 (M := M) (e20 z0 z1) (e11) (e12) (fun w3 : M => (e2 z0 w3)) ((fun w3 : M => v6 z0 z1 w3))
  have v8 := fun z0 : M => p1537 (M := M) (e17 z0) (a1) (e11) (e12) (fun w4 : M => (e3 z0)) ((fun w4 : M => v7 z0 w4))
  have v9 := p1539 (M := M) (a0) ((show M from (t63 (M := M) (a1) (e11)))) (e12) (fun w3 : M => (e4 w3)) ((fun w3 : M => v8 w3))
  have v10 : (e14) := (show (e14) from v9)
  have v11 := ((v3) (v10))
  exact v11
-- Actual MMB 2368 lmemssn
theorem p2375 (a0 : M)  : (t1 (t144 (a0) (t28 (M := M)))) := by
  let e0  : M := (t28 (M := M))
  let e1  : M := (t143 (e0))
  let e2  : Prop := (t10 (M := M) (e1) (e0))
  let e3  : Prop := (t144 (a0) (e0))
  let e5  : Prop := (t16 (M := M) (a0) ((show (M → Prop) from (t120 (e0)))))
  let e6  : Prop := (t3 (e3) (e5))
  let e7  : Prop := (t0 (e2) (e6))
  have v0 := p2020 (M := M) (a0) (e1) (e0)
  have v1 : (e7) := (show (e7) from v0)
  have v2 := p2366 (M := M)
  have v3 := b3 (e2) (e6) (v1) (v2)
  have v4 := p2044 (M := M) (a0)
  have v5 := p124 (e5) (e3) (v3) (v4)
  exact v5
-- Actual MMB 2376 lmemS
theorem p2376 (a0 : M) (a1 : M) (a2 : M)  : (t3 (t144 (a0) (t131 (a1) (a2))) (t4 (t10 (M := M) (a0) (a1)) (t144 (a0) (a2)))) := by
  let e0  : M := (t131 (a1) (a2))
  let e1  : Prop := (t144 (a0) (e0))
  let e2  : M := (t143 (a2))
  let e3  : M := (t123 (a1) (e2))
  let e5  : Prop := (t16 (M := M) (a0) ((show (M → Prop) from (t120 (e3)))))
  let e8  : Prop := (t4 ((show Prop from (t10 (M := M) (a0) (a1)))) ((show Prop from (t144 (a0) (a2)))))
  let e9  : M := (t143 (e0))
  let e12  : Prop := (t0 ((show Prop from (t10 (M := M) (e9) (e3)))) ((show Prop from (t3 (e1) (e5)))))
  let e13  : Prop := (t3 (e5) (e8))
  have v0 := p149 (e1) (e5) (e8)
  have v1 := p2020 (M := M) (a0) (e9) (e3)
  have v2 : (e12) := (show (e12) from v1)
  have v3 := p2367 (M := M) (a1) (a2)
  have v4 := ((v2) (v3))
  have v5 := ((v0) (v4))
  have v6 := p2121 (M := M) (a0) (a1) (e2)
  have v7 : (e13) := (show (e13) from v6)
  have v8 := ((v5) (v7))
  exact v8
-- Actual MMB 2377 lmem1
end ZF207.MM0ModelReplay
