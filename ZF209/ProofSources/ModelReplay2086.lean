module
public import ModelReplay2038
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2039 bndext
theorem p2040 (a0 : M) (a1 : M)  : (t0 (t18 (M := M) (t120 (a0)) (t120 (a1))) (t47 (M := M) (a0) (a1))) := by
  let e0  : M := (t31 (M := M))
  let e1  : M := (t55 (M := M) (a0) (a1))
  let e2  : M := (t117 (M := M) (e0) (e1))
  let e3  : M := (t57 (M := M) (a0) (e2))
  let e4  : M := (t57 (M := M) (a1) (e2))
  let e13  : Prop := (t47 (M := M) (e3) (e4))
  let e20  : (M → Prop) := (t120 (a0))
  let e21 (u0 : M) : Prop := (t16 (M := M) u0 (e20))
  let e22  : (M → Prop) := (t120 (a1))
  let e23 (u0 : M) : Prop := (t16 (M := M) u0 (e22))
  let e24 (u0 : M) : Prop := (t0 (e21 u0) (e23 u0))
  let e25 (u0 : M) : Prop := (t48 (M := M) u0 (e1))
  let e26 (u0 : M) : Prop := (t0 (e25 u0) (e24 u0))
  let e27  : Prop := (t18 (M := M) (e20) (e22))
  let e28  : Prop := (t8 (M := M) (fun x0_0 : M => (e26 x0_0)))
  let e29  : Prop := (t0 (e27) (e28))
  have v0 := p851 (M := M) (e3) (a0) (e4) (a1)
  have v1 := p1099 (M := M) (a0) (e2)
  have v2 := p897 (M := M) (a0) (e1) (e2)
  have v3 := p1048 (M := M) (a0) (a1)
  have v4 := ((v2) (v3))
  have v5 := p1974 (M := M) (e0) (e1)
  have v6 := p920 (M := M)
  have v7 := ((v5) (v6))
  have v8 := ((v4) (v7))
  have v9 := ((v1) (v8))
  have v10 := ((v0) (v9))
  have v11 := p1099 (M := M) (a1) (e2)
  have v12 := p897 (M := M) (a1) (e1) (e2)
  have v13 := p1049 (M := M) (a0) (a1)
  have v14 := ((v12) (v13))
  have v15 := ((v14) (v7))
  have v16 := ((v11) (v15))
  have v17 := ((v10) (v16))
  have v18 := p2038 (M := M) (a0) (a1) (e1)
  have v19 := fun z0 : M => b0 (e24 z0) (e25 z0)
  have v20 := p337 (M := M) (fun w0 : M => (e24 w0)) (fun w0 : M => (e26 w0)) ((fun w0 : M => v19 w0))
  have v21 : (e29) := (show (e29) from v20)
  have v22 := p10 (e27) (e28) (e13) (v18) (v21)
  have v23 := p153 (e27) (e13) ((show Prop from (t47 (M := M) (a0) (a1)))) (v17) (v22)
  exact v23
-- Actual MMB 2041 axext
theorem p2041 (a0 : M) (a1 : M)  : (t0 (t17 (M := M) (t120 (a0)) (t120 (a1))) (t10 (M := M) (a0) (a1))) := by
  let e0  : (M → Prop) := (t120 (a0))
  let e1  : (M → Prop) := (t120 (a1))
  let e2  : Prop := (t17 (M := M) (e0) (e1))
  have v0 := p2040 (M := M) (a0) (a1)
  have v1 := p611 (M := M) (e0) (e1)
  have v2 := p10 (e2) ((show Prop from (t18 (M := M) (e0) (e1)))) ((show Prop from (t47 (M := M) (a0) (a1)))) (v0) (v1)
  have v3 := p2040 (M := M) (a1) (a0)
  have v4 := p612 (M := M) (e0) (e1)
  have v5 := p10 (e2) ((show Prop from (t18 (M := M) (e1) (e0)))) ((show Prop from (t47 (M := M) (a1) (a0)))) (v3) (v4)
  have v6 := p874 (M := M) (e2) (a0) (a1) (v2) (v5)
  exact v6
-- Actual MMB 2042 nsinj
theorem p2042 (a0 : M) (a1 : M)  : (t3 (t17 (M := M) (t120 (a0)) (t120 (a1))) (t10 (M := M) (a0) (a1))) := by
  have v0 := p2041 (M := M) (a0) (a1)
  have v1 := p2016 (M := M) (a0) (a1)
  have v2 := p112 ((show Prop from (t17 (M := M) ((show (M → Prop) from (t120 (a0)))) ((show (M → Prop) from (t120 (a1))))))) ((show Prop from (t10 (M := M) (a0) (a1)))) (v0) (v1)
  exact v2
-- Actual MMB 2043 ellt
theorem p2043 (a0 : M) (a1 : M)  : (t0 (t16 (M := M) (a0) (t120 (a1))) (t48 (M := M) (a0) (a1))) := by
  let e0  : M := (t119 (M := M) (a1) (a0))
  let e1  : Prop := (t48 (M := M) (a0) (a1))
  let e2  : M := (t31 (M := M))
  let e3  : M := (t57 (M := M) (e0) (e2))
  let e4  : M := (t28 (M := M))
  let e5  : Prop := (t10 (M := M) (e3) (e4))
  let e6  : Prop := (t1 (e1))
  let e8  : Prop := (t51 (M := M) (e3))
  let e10  : Prop := (t0 ((show Prop from (t0 (e6) (e5)))) ((show Prop from (t0 (e8) (e1)))))
  let e11  : M := (t117 (M := M) (e2) (a0))
  let e13  : Prop := (t10 (M := M) (e0) (e4))
  let e14  : Prop := (t48 (M := M) (a1) (e11))
  let e16  : Prop := (t0 ((show Prop from (t13 (M := M) (e11) (e4)))) ((show Prop from (t3 (e13) (e14)))))
  let e20  : Prop := (t47 (M := M) (a1) (a0))
  let e22  : Prop := (t62 (M := M) (e0))
  have v0 := p2017 (M := M) (a0) (a1)
  have v1 := p1198 (M := M) (e0)
  have v2 := p41 (e1) (e5)
  have v3 : (e10) := (show (e10) from v2)
  have v4 := p932 (M := M) (a1) (a0)
  have v5 := p1081 (M := M) (e2)
  have v6 := p1109 (M := M) (a1) (e11)
  have v7 : (e16) := (show (e16) from v6)
  have v8 := p1973 (M := M) (a0)
  have v9 := ((v7) (v8))
  have v10 := p1974 (M := M) (e2) (a0)
  have v11 := p920 (M := M)
  have v12 := ((v10) (v11))
  have v13 := p897 (M := M) (a1) (a0) (e11)
  have v14 := p7 (e20) ((show Prop from (t48 (M := M) (a0) (e11)))) (e14) (v12) (v13)
  have v15 := p154 (e20) (e14) (e13) (v9) (v14)
  have v16 := p1067 (M := M) (e20) (e0) (e4) (e2) (v15)
  have v17 := p362 (M := M) (e20) (e3) ((show M from (t57 (M := M) (e4) (e2)))) (e4) (v5) (v16)
  have v18 := p156 (e6) (e20) (e5) (v4) (v17)
  have v19 := ((v3) (v18))
  have v20 := p155 (e22) (e8) (e1) (v1) (v19)
  have v21 := p155 ((show Prop from (t16 (M := M) (a0) ((show (M → Prop) from (t120 (a1))))))) (e22) (e1) (v0) (v20)
  exact v21
-- Actual MMB 2044 el02
theorem p2044 (a0 : M)  : (t1 (t16 (M := M) (a0) (t120 (t28 (M := M))))) := by
  let e0  : M := (t28 (M := M))
  have v0 := p2043 (M := M) (a0) (e0)
  have v1 := p904 (M := M) (a0)
  have v2 := p48 ((show Prop from (t48 (M := M) (a0) (e0)))) ((show Prop from (t16 (M := M) (a0) ((show (M → Prop) from (t120 (e0))))))) (v0) (v1)
  exact v2
-- Actual MMB 2046 ss01
theorem p2046 (a0 : (M → Prop))  : (t18 (M := M) (t120 (t28 (M := M))) (a0)) := by
  let e1  : (M → Prop) := (t120 ((show M from (t28 (M := M)))))
  let e2 (u0 : M) : Prop := (t16 (M := M) u0 (e1))
  let e3 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e4 (u0 : M) : Prop := (t1 (e2 u0))
  let e5 (u0 : M) : Prop := (t0 (e2 u0) (e3 u0))
  let e6  : Prop := (t18 (M := M) (e1) (a0))
  have v0 := fun z0 : M => p22 (e2 z0) (e3 z0)
  have v1 := fun z0 : M => p2044 (M := M) z0
  have v2 := fun z0 : M => b3 (e4 z0) (e5 z0) (v0 z0) (v1 z0)
  have v3 := b325 (M := M) (fun w0 : M => (e5 w0)) ((fun w0 : M => v2 w0))
  have v4 : (e6) := (show (e6) from v3)
  exact v4
-- Actual MMB 2047 ss02
theorem p2047 (a0 : (M → Prop))  : (t3 (t18 (M := M) (a0) (t120 (t28 (M := M)))) (t17 (M := M) (a0) (t120 (t28 (M := M))))) := by
  let e1  : (M → Prop) := (t120 ((show M from (t28 (M := M)))))
  let e2  : Prop := (t18 (M := M) (a0) (e1))
  let e4  : Prop := (t17 (M := M) (a0) (e1))
  have v0 := p2046 (M := M) (a0)
  have v1 := p613 (M := M) (a0) (e1)
  have v2 := p7 (e2) ((show Prop from (t18 (M := M) (e1) (a0)))) (e4) (v0) (v1)
  have v3 := p2046 (M := M) (e1)
  have v4 := p603 (M := M) (a0) (e1) (e1)
  have v5 := p122 (e4) ((show Prop from (t18 (M := M) (e1) (e1)))) (e2) (v3) (v4)
  have v6 := p112 (e2) (e4) (v2) (v5)
  exact v6
-- Actual MMB 2048 eq0al
theorem p2048 (a0 : (M → Prop))  : (t3 (t17 (M := M) (a0) (t120 (t28 (M := M)))) (t8 (M := M) (fun x1_0 : M => (t1 (t16 (M := M) x1_0 (a0)))))) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e2  : (M → Prop) := (t120 ((show M from (t28 (M := M)))))
  let e3 (u0 : M) : Prop := (t16 (M := M) u0 (e2))
  let e4 (u0 : M) : Prop := (t3 (e0 u0) (e3 u0))
  let e5  : Prop := (t7)
  let e6 (u0 : M) : Prop := (t3 (e0 u0) (e5))
  let e7 (u0 : M) : Prop := (t1 (e0 u0))
  let e8 (u0 : M) : Prop := (t1 (e3 u0))
  let e9 (u0 : M) : Prop := (t3 (e3 u0) (e5))
  let e10 (u0 : M) : Prop := (t3 (e4 u0) (e6 u0))
  let e11 (u0 : M) : Prop := (t3 (e6 u0) (e7 u0))
  let e12 (u0 : M) : Prop := (t3 (e4 u0) (e7 u0))
  let e13 (u0 : M) : Prop := (t0 (e11 u0) (e12 u0))
  let e16  : Prop := (t3 ((show Prop from (t17 (M := M) (a0) (e2)))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e7 x0_0))))))
  have v0 := fun z0 : M => p149 (e4 z0) (e6 z0) (e7 z0)
  have v1 := fun z0 : M => p238 (e0 z0) (e3 z0) (e5)
  have v2 := fun z0 : M => p323 (e3 z0)
  have v3 := fun z0 : M => p2044 (M := M) z0
  have v4 := fun z0 : M => p118 (e8 z0) (e9 z0) (v2 z0) (v3 z0)
  have v5 := fun z0 : M => b3 (e9 z0) (e10 z0) (v1 z0) (v4 z0)
  have v6 := fun z0 : M => b3 (e10 z0) (e13 z0) (v0 z0) (v5 z0)
  have v7 := fun z0 : M => p323 (e0 z0)
  have v8 := fun z0 : M => b3 (e11 z0) (e12 z0) (v6 z0) (v7 z0)
  have v9 := p367 (M := M) (fun w0 : M => (e4 w0)) (fun w0 : M => (e7 w0)) ((fun w0 : M => v8 w0))
  have v10 : (e16) := (show (e16) from v9)
  exact v10
-- Actual MMB 2049 sseq0
theorem p2067 (a0 : (M → Prop))  : (t17 (M := M) (t75 (M := M) (t120 (t28 (M := M))) (a0)) (t120 (t28 (M := M)))) := by
  let e1  : (M → Prop) := (t120 ((show M from (t28 (M := M)))))
  let e2  : (M → Prop) := (t75 (M := M) (e1) (a0))
  let e3 (u0 : M) : M := (t64 (M := M) u0)
  let e4 (u0 : M) : Prop := (t16 (M := M) (e3 u0) (e1))
  let e5 (u0 : M) : Prop := (t16 (M := M) u0 (e2))
  let e6 (u0 : M) : Prop := (t1 (e5 u0))
  have v0 := p2048 (M := M) (e2)
  have v1 := fun z0 : M => p1361 (M := M) (e1) (a0) z0
  have v2 := fun z0 : M => p2044 (M := M) (e3 z0)
  have v3 := fun z0 : M => p48 (e4 z0) (e5 z0) (v1 z0) (v2 z0)
  have v4 := b325 (M := M) (fun w0 : M => (e6 w0)) ((fun w0 : M => v3 w0))
  have v5 := p118 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e6 x0_0))))) ((show Prop from (t17 (M := M) (e2) (e1)))) (v0) (v4)
  exact v5
-- Actual MMB 2068 xp02
theorem p2069 (a0 : (M → Prop))  : (t3 (t17 (M := M) (t76 (M := M) (a0)) (t120 (t28 (M := M)))) (t17 (M := M) (a0) (t120 (t28 (M := M))))) := by
  let e0  : (M → Prop) := (t76 (M := M) (a0))
  let e2  : (M → Prop) := (t120 ((show M from (t28 (M := M)))))
  let e4  : Prop := (t18 (M := M) (e0) (e2))
  let e5  : Prop := (t17 (M := M) (a0) (e2))
  let e10  : (M → Prop) := (t22 (M := M))
  let e11  : (M → Prop) := (t75 (M := M) (e2) (e10))
  let e12  : Prop := (t18 (M := M) (a0) (e11))
  have v0 := p151 ((show Prop from (t17 (M := M) (e0) (e2)))) (e4) (e5)
  have v1 := p2047 (M := M) (e0)
  have v2 := ((v0) (v1))
  have v3 := p149 (e4) (e12) (e5)
  have v4 := p1398 (M := M) (e2) (a0)
  have v5 := ((v3) (v4))
  have v6 := p149 (e12) ((show Prop from (t18 (M := M) (a0) (e2)))) (e5)
  have v7 := p605 (M := M) (a0) (e11) (e2)
  have v8 := p2067 (M := M) (e10)
  have v9 := ((v7) (v8))
  have v10 := ((v6) (v9))
  have v11 := p2047 (M := M) (a0)
  have v12 := ((v10) (v11))
  have v13 := ((v5) (v12))
  have v14 := ((v2) (v13))
  exact v14
-- Actual MMB 2070 rneq0
theorem p2071   : (t17 (M := M) (t76 (M := M) (t120 (t28 (M := M)))) (t120 (t28 (M := M)))) := by
  let e1  : (M → Prop) := (t120 ((show M from (t28 (M := M)))))
  have v0 := p2069 (M := M) (e1)
  have v1 := p554 (M := M) (e1)
  have v2 := p118 ((show Prop from (t17 (M := M) (e1) (e1)))) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t76 (M := M) (e1)))) (e1)))) (v0) (v1)
  exact v2
-- Actual MMB 2072 rn0
theorem p2074   : (t72 (M := M) (t120 (t28 (M := M)))) := by
  let e0 (u0 : M) (u1 : M) : M := (t63 (M := M) u0 u1)
  let e2  : (M → Prop) := (t120 ((show M from (t28 (M := M)))))
  let e3 (u0 : M) (u1 : M) : Prop := (t16 (M := M) (e0 u0 u1) (e2))
  let e4 (u0 : M) (u1 : M) : M := (t63 (M := M) u0 u1)
  let e5 (u0 : M) (u1 : M) : Prop := (t16 (M := M) (e4 u0 u1) (e2))
  let e6 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e7 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e5 u0 u2) (e6 u1 u2))
  let e8 (u0 : M) (u1 : M) : Prop := (t1 (e3 u0 u1))
  let e9 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e3 u0 u1) (e7 u0 u1 u2))
  let e10 (u0 : M) (u1 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e9 u0 u1 x0_0)))
  let e11 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e10 u0 x0_0)))
  let e12  : Prop := (t72 (M := M) (e2))
  have v0 := fun z0 : M => fun z1 : M => fun z2 : M => p22 (e3 z0 z1) (e7 z0 z1 z2)
  have v1 := fun z0 : M => fun z1 : M => p2044 (M := M) (e0 z0 z1)
  have v2 := fun z0 : M => fun z1 : M => fun z2 : M => b3 (e8 z0 z1) (e9 z0 z1 z2) (v0 z0 z1 z2) (v1 z0 z1)
  have v3 := fun z0 : M => fun z1 : M => b325 (M := M) (fun w0 : M => (e9 z0 z1 w0)) ((fun w0 : M => v2 z0 z1 w0))
  have v4 := fun z0 : M => b325 (M := M) (fun w0 : M => (e10 z0 w0)) ((fun w0 : M => v3 z0 w0))
  have v5 := b325 (M := M) (fun w0 : M => (e11 w0)) ((fun w0 : M => v4 w0))
  have v6 : (e12) := (show (e12) from v5)
  exact v6
-- Actual MMB 2075 rapp01

end ZF209.MM0ModelReplay
