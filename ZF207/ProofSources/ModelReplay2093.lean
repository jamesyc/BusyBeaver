module
public import ModelReplay2086
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2087 elobind
theorem p2088 (a0 : M)  : (t3 (t16 (M := M) (a0) (t120 (t30 (M := M)))) (t10 (M := M) (a0) (t28 (M := M)))) := by
  let e0  : M := (t30 (M := M))
  let e1  : (M → Prop) := (t120 (e0))
  let e2  : Prop := (t16 (M := M) (a0) (e1))
  let e4  : M := (t28 (M := M))
  let e5  : Prop := (t10 (M := M) (a0) (e4))
  let e7  : Prop := (t16 (M := M) (e4) (e1))
  have v0 := p921 (M := M) (a0)
  have v1 := p2043 (M := M) (a0) (e0)
  have v2 := p153 (e2) ((show Prop from (t48 (M := M) (a0) (e0)))) (e5) (v0) (v1)
  have v3 := p2025 (M := M) (e0)
  have v4 := p1242 (M := M)
  have v5 := p118 ((show Prop from (t62 (M := M) (e0)))) (e7) (v3) (v4)
  have v6 := p572 (M := M) (e1) (a0) (e4)
  have v7 := p122 (e5) (e7) (e2) (v5) (v6)
  have v8 := p112 (e2) (e5) (v2) (v7)
  exact v8
-- Actual MMB 2089 elpow2
theorem p2089 (a0 : M) (a1 : M)  : (t3 (t16 (M := M) (a0) (t120 (t117 (M := M) (t31 (M := M)) (a1)))) (t10 (M := M) (a0) (a1))) := by
  let e1  : M := (t117 (M := M) ((show M from (t31 (M := M)))) (a1))
  let e4  : M := (t30 (M := M))
  let e5  : M := (t118 (M := M) (e4) (a1))
  let e7  : Prop := (t16 (M := M) (a0) ((show (M → Prop) from (t120 (e5)))))
  let e8  : Prop := (t10 (M := M) (a0) (a1))
  let e14  : Prop := (t47 (M := M) (a1) (a0))
  let e15  : M := (t46 (M := M) (a0) (a1))
  let e17  : Prop := (t16 (M := M) (e15) ((show (M → Prop) from (t120 (e4)))))
  let e18  : Prop := (t2 (e14) (e17))
  let e22  : Prop := (t47 (M := M) (a0) (a1))
  let e23  : Prop := (t2 (e14) (e22))
  have v0 := p151 ((show Prop from (t16 (M := M) (a0) ((show (M → Prop) from (t120 (e1))))))) (e7) (e8)
  have v1 := p2020 (M := M) (a0) (e5) (e1)
  have v2 := p1996 (M := M) (a1)
  have v3 := ((v1) (v2))
  have v4 := ((v0) (v3))
  have v5 := p149 (e7) (e18) (e8)
  have v6 := p2027 (M := M) (a0) (e4) (a1)
  have v7 := ((v5) (v6))
  have v8 := p152 (e18) (e23) (e8)
  have v9 := p152 (e17) ((show Prop from (t10 (M := M) (e15) ((show M from (t28 (M := M))))))) (e22)
  have v10 := p2088 (M := M) (e15)
  have v11 := ((v9) (v10))
  have v12 := p939 (M := M) (a0) (a1)
  have v13 := ((v11) (v12))
  have v14 := p204 (e14) (e17) (e22) (v13)
  have v15 := ((v8) (v14))
  have v16 := p149 (e8) ((show Prop from (t10 (M := M) (a1) (a0)))) (e23)
  have v17 := p345 (M := M) (a0) (a1)
  have v18 := ((v16) (v17))
  have v19 := p876 (M := M) (a1) (a0)
  have v20 := ((v18) (v19))
  have v21 := ((v15) (v20))
  have v22 := ((v7) (v21))
  have v23 := ((v4) (v22))
  exact v23
-- Actual MMB 2090 finns
theorem p2090 (a0 : M)  : (t49 (M := M) (t120 (a0))) := by
  let e0  : (M → Prop) := (t120 (a0))
  let e1 (u0 : M) : Prop := (t48 (M := M) u0 (a0))
  let e2  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e3 (u0 : M) : Prop := (t16 (M := M) u0 (e0))
  let e4 (u0 : M) : Prop := (t0 (e3 u0) (e1 u0))
  let e6  : Prop := (t18 (M := M) (e0) (e2))
  let e7  : Prop := (t49 (M := M) (e2))
  let e8  : Prop := (t49 (M := M) (e0))
  have v0 := p972 (M := M) (e0) (e2)
  have v1 := p699 (M := M) (e0) (fun w1 : M => (e1 w1))
  have v2 := fun z0 : M => p2043 (M := M) z0 (a0)
  have v3 := b325 (M := M) (fun w0 : M => (e4 w0)) ((fun w0 : M => v2 w0))
  have v4 := p117 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e4 x0_0))))) (e6) (v1) (v3)
  have v5 := b3 (e6) ((show Prop from (t0 (e7) (e8)))) (v0) (v4)
  have v6 := p973 (M := M) (a0)
  have v7 := b3 (e7) (e8) (v5) (v6)
  exact v7
-- Actual MMB 2091 lowereqd
theorem p2091 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (h0 : (t0 (a0) (t17 (M := M) (a1) (a2)))) : (t0 (a0) (t10 (M := M) (t121 (a1)) (t121 (a2)))) := by
  let e0 (u0 : M) : (M → Prop) := (t120 u0)
  let e1 (u0 : M) : Prop := (t17 (M := M) (e0 u0) (a1))
  let e2 (u0 : M) : Prop := (t17 (M := M) (e0 u0) (a2))
  let e8  : Prop := (t0 (a0) ((show Prop from (t10 (M := M) ((show M from (t121 (a1)))) ((show M from (t121 (a2))))))))
  have v0 := fun z0 : M => p581 (M := M) (a0) (e0 z0) (a1) (a2) (h0)
  have v1 := p584 (M := M) (a0) (fun w1 : M => (e1 w1)) (fun w1 : M => (e2 w1)) ((fun w1 : M => v0 w1))
  have v2 := p748 (M := M) (a0) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e1 x0_0))))) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e2 x0_0))))) (v1)
  have v3 : (e8) := (show (e8) from v2)
  exact v3
-- Actual MMB 2092 lowereq
theorem p2092 (a0 : (M → Prop)) (a1 : (M → Prop))  : (t0 (t17 (M := M) (a0) (a1)) (t10 (M := M) (t121 (a0)) (t121 (a1)))) := by
  let e0  : Prop := (t17 (M := M) (a0) (a1))
  have v0 := p8 (e0)
  have v1 := p2091 (M := M) (e0) (a0) (a1) (v0)
  exact v1
-- Actual MMB 2093 nflower

end ZF207.MM0ModelReplay
