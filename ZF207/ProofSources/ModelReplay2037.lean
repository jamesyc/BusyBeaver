module
public import ModelNumericSetDefinitions
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2000 shlpow2dvd
theorem p2000 (a0 : M) (a1 : M)  : (t58 (M := M) (t117 (M := M) (t31 (M := M)) (a1)) (t118 (M := M) (a0) (a1))) := by
  let e1  : M := (t117 (M := M) ((show M from (t31 (M := M)))) (a1))
  let e3  : Prop := (t58 (M := M) (e1) ((show M from (t118 (M := M) (a0) (a1)))))
  have v0 := p1130 (M := M) (e1) (a0)
  have v1 : (e3) := (show (e3) from v0)
  exact v1
-- Actual MMB 2001 shl2dvd
theorem p2001 (a0 : M) (a1 : M)  : (t0 (t48 (M := M) (t28 (M := M)) (a1)) (t58 (M := M) (t31 (M := M)) (t118 (M := M) (a0) (a1)))) := by
  let e0  : M := (t31 (M := M))
  let e1  : M := (t117 (M := M) (e0) (a1))
  let e2  : M := (t118 (M := M) (a0) (a1))
  let e3  : Prop := (t58 (M := M) (e0) (e1))
  let e5  : Prop := (t58 (M := M) (e0) (e2))
  have v0 := p1978 (M := M) (e0) (a1)
  have v1 := p2000 (M := M) (a0) (a1)
  have v2 := p1132 (M := M) (e0) (e1) (e2)
  have v3 := p7 (e3) ((show Prop from (t58 (M := M) (e1) (e2)))) (e5) (v1) (v2)
  have v4 := p11 ((show Prop from (t48 (M := M) ((show M from (t28 (M := M)))) (a1)))) (e3) (e5) (v0) (v3)
  exact v4
-- Actual MMB 2002 shr01
theorem p2003 (a0 : M)  : (t10 (M := M) (t119 (M := M) (a0) (t28 (M := M))) (a0)) := by
  let e0  : M := (t28 (M := M))
  let e1  : M := (t119 (M := M) (a0) (e0))
  let e2  : M := (t30 (M := M))
  let e3  : M := (t56 (M := M) (a0) (e2))
  let e4  : M := (t31 (M := M))
  let e5  : M := (t117 (M := M) (e4) (e0))
  let e8  : Prop := (t0 ((show Prop from (t10 (M := M) (e5) (e2)))) ((show Prop from (t10 (M := M) (e1) (e3)))))
  have v0 := p342 (M := M) (e1) (e3) (a0)
  have v1 := p1064 (M := M) (a0) (e5) (e2)
  have v2 : (e8) := (show (e8) from v1)
  have v3 := p1965 (M := M) (e4)
  have v4 := ((v2) (v3))
  have v5 := ((v0) (v4))
  have v6 := p1083 (M := M) (a0)
  have v7 := ((v5) (v6))
  exact v7
-- Actual MMB 2004 shr12
theorem p2004 (a0 : M)  : (t10 (M := M) (t119 (M := M) (a0) (t30 (M := M))) (t56 (M := M) (a0) (t31 (M := M)))) := by
  let e0  : M := (t31 (M := M))
  let e1  : M := (t30 (M := M))
  let e2  : M := (t117 (M := M) (e0) (e1))
  let e3  : Prop := (t10 (M := M) (e2) (e0))
  let e6  : Prop := (t10 (M := M) ((show M from (t119 (M := M) (a0) (e1)))) ((show M from (t56 (M := M) (a0) (e0)))))
  let e7  : Prop := (t0 (e3) (e6))
  have v0 := p1064 (M := M) (a0) (e2) (e0)
  have v1 : (e7) := (show (e7) from v0)
  have v2 := p1968 (M := M) (e0)
  have v3 := b3 (e3) (e6) (v1) (v2)
  exact v3
-- Actual MMB 2005 shrshr
theorem p2005 (a0 : M) (a1 : M) (a2 : M)  : (t10 (M := M) (t119 (M := M) (t119 (M := M) (a0) (a1)) (a2)) (t119 (M := M) (a0) (t44 (M := M) (a1) (a2)))) := by
  let e1  : M := (t119 (M := M) ((show M from (t119 (M := M) (a0) (a1)))) (a2))
  let e2  : M := (t31 (M := M))
  let e3  : M := (t117 (M := M) (e2) (a1))
  let e4  : M := (t117 (M := M) (e2) (a2))
  let e5  : M := (t45 (M := M) (e3) (e4))
  let e6  : M := (t56 (M := M) (a0) (e5))
  let e7  : M := (t44 (M := M) (a1) (a2))
  let e8  : M := (t119 (M := M) (a0) (e7))
  let e9  : Prop := (t10 (M := M) (e1) (e6))
  let e13  : M := (t117 (M := M) (e2) (e7))
  let e15  : Prop := (t0 ((show Prop from (t10 (M := M) (e13) (e5)))) ((show Prop from (t10 (M := M) (e8) (e6)))))
  have v0 := p344 (M := M) (e1) (e6) (e8)
  have v1 := p1110 (M := M) (a0) (e3) (e4)
  have v2 : (e9) := (show (e9) from v1)
  have v3 := ((v0) (v2))
  have v4 := p1064 (M := M) (a0) (e13) (e5)
  have v5 : (e15) := (show (e15) from v4)
  have v6 := p1975 (M := M) (e2) (a1) (a2)
  have v7 := ((v5) (v6))
  have v8 := ((v3) (v7))
  exact v8
-- Actual MMB 2006 shrmodadd1
theorem p2011 (a0 : M) (a1 : M)  : (t10 (M := M) (t119 (M := M) (t118 (M := M) (a0) (a1)) (a1)) (a0)) := by
  let e1  : M := (t117 (M := M) ((show M from (t31 (M := M)))) (a1))
  let e3  : Prop := (t13 (M := M) (e1) ((show M from (t28 (M := M)))))
  let e6  : Prop := (t10 (M := M) ((show M from (t119 (M := M) ((show M from (t118 (M := M) (a0) (a1)))) (a1)))) (a0))
  let e7  : Prop := (t0 (e3) (e6))
  have v0 := p1093 (M := M) (a0) (e1)
  have v1 : (e7) := (show (e7) from v0)
  have v2 := p1973 (M := M) (a1)
  have v3 := b3 (e3) (e6) (v1) (v2)
  exact v3
-- Actual MMB 2012 shrshl1
theorem p2012 (a0 : M) (a1 : M) (a2 : M)  : (t0 (t47 (M := M) (a2) (a1)) (t10 (M := M) (t119 (M := M) (t118 (M := M) (a0) (a1)) (a2)) (t118 (M := M) (a0) (t46 (M := M) (a1) (a2))))) := by
  let e0  : M := (t46 (M := M) (a1) (a2))
  let e1  : M := (t118 (M := M) (a0) (e0))
  let e2  : Prop := (t47 (M := M) (a2) (a1))
  let e3  : M := (t44 (M := M) (e0) (a2))
  let e4  : M := (t118 (M := M) (a0) (a1))
  let e6  : M := (t118 (M := M) (e1) (a2))
  have v0 := p2011 (M := M) (e1) (a2)
  have v1 := p1998 (M := M) (a0) (e0) (a2)
  have v2 := p861 (M := M) (a1) (a2)
  have v3 := p356 (M := M) (e2) (e3) (a1) (v2)
  have v4 := p1986 (M := M) (e2) (a0) (a1) (e3) (v3)
  have v5 := p363 (M := M) (e2) (e4) ((show M from (t118 (M := M) (a0) (e3)))) (e6) (v1) (v4)
  have v6 := p1990 (M := M) (e2) (e4) (e6) (a2) (v5)
  have v7 := p362 (M := M) (e2) ((show M from (t119 (M := M) (e4) (a2)))) ((show M from (t119 (M := M) (e6) (a2)))) (e1) (v0) (v6)
  exact v7
-- Actual MMB 2013 shrshl2
theorem p2013 (a0 : M) (a1 : M) (a2 : M)  : (t0 (t47 (M := M) (a1) (a2)) (t10 (M := M) (t119 (M := M) (t118 (M := M) (a0) (a1)) (a2)) (t119 (M := M) (a0) (t46 (M := M) (a2) (a1))))) := by
  let e0  : M := (t118 (M := M) (a0) (a1))
  let e1  : M := (t119 (M := M) (e0) (a1))
  let e2  : M := (t46 (M := M) (a2) (a1))
  let e4  : M := (t119 (M := M) (e1) (e2))
  let e7  : Prop := (t47 (M := M) (a1) (a2))
  let e8  : M := (t44 (M := M) (a1) (e2))
  let e9  : M := (t119 (M := M) (e0) (a2))
  have v0 := p1991 (M := M) (e1) (a0) (e2)
  have v1 := p2011 (M := M) (a0) (a1)
  have v2 := ((v0) (v1))
  have v3 := p2005 (M := M) (e0) (a1) (e2)
  have v4 := p860 (M := M) (a1) (a2)
  have v5 := p356 (M := M) (e7) (e8) (a2) (v4)
  have v6 := p1992 (M := M) (e7) (e0) (a2) (e8) (v5)
  have v7 := p363 (M := M) (e7) (e9) ((show M from (t119 (M := M) (e0) (e8)))) (e4) (v3) (v6)
  have v8 := p362 (M := M) (e7) (e9) (e4) ((show M from (t119 (M := M) (a0) (e2)))) (v2) (v7)
  exact v8
-- Actual MMB 2014 shreq0
theorem p2015 (a0 : Prop) (a1 : M) (a2 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) : (t0 (a0) (t17 (M := M) (t120 (a1)) (t120 (a2)))) := by
  let e0 (u0 : M) : M := (t119 (M := M) (a1) u0)
  let e1 (u0 : M) : M := (t119 (M := M) (a2) u0)
  let e2 (u0 : M) : Prop := (t62 (M := M) (e0 u0))
  let e3 (u0 : M) : Prop := (t62 (M := M) (e1 u0))
  let e7  : Prop := (t0 (a0) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t120 (a1)))) ((show (M → Prop) from (t120 (a2))))))))
  have v0 := fun z0 : M => p1990 (M := M) (a0) (a1) (a2) z0 (h0)
  have v1 := fun z0 : M => p1187 (M := M) (a0) (e0 z0) (e1 z0) (v0 z0)
  have v2 := p584 (M := M) (a0) (fun w1 : M => (e2 w1)) (fun w1 : M => (e3 w1)) ((fun w1 : M => v1 w1))
  have v3 : (e7) := (show (e7) from v2)
  exact v3
-- Actual MMB 2016 nseq
theorem p2016 (a0 : M) (a1 : M)  : (t0 (t10 (M := M) (a0) (a1)) (t17 (M := M) (t120 (a0)) (t120 (a1)))) := by
  let e0  : Prop := (t10 (M := M) (a0) (a1))
  have v0 := p8 (e0)
  have v1 := p2015 (M := M) (e0) (a0) (a1) (v0)
  exact v1
-- Actual MMB 2017 elnel
theorem p2017 (a0 : M) (a1 : M)  : (t3 (t16 (M := M) (a0) (t120 (a1))) (t62 (M := M) (t119 (M := M) (a1) (a0)))) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a0))
  let e1 (u0 : M) : M := (t119 (M := M) (a1) u0)
  let e2  : M := (t119 (M := M) (a1) (a0))
  let e3 (u0 : M) : Prop := (t62 (M := M) (e1 u0))
  let e4  : Prop := (t62 (M := M) (e2))
  let e7  : Prop := (t3 ((show Prop from (t16 (M := M) (a0) ((show (M → Prop) from (t120 (a1))))))) (e4))
  have v0 := fun z0 : M => p8 (e0 z0)
  have v1 := fun z0 : M => p1992 (M := M) (e0 z0) (a1) z0 (a0) (v0 z0)
  have v2 := fun z0 : M => p1187 (M := M) (e0 z0) (e1 z0) (e2) (v1 z0)
  have v3 := p593 (M := M) (a0) (fun w0 : M => (e3 w0)) (e4) ((fun w0 : M => v2 w0))
  have v4 : (e7) := (show (e7) from v3)
  exact v4
-- Actual MMB 2018 elneqd
theorem p2018 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) (h1 : (t0 (a0) (t10 (M := M) (a3) (a4)))) : (t0 (a0) (t3 (t16 (M := M) (a1) (t120 (a3))) (t16 (M := M) (a2) (t120 (a4))))) := by
  have v0 := p2015 (M := M) (a0) (a3) (a4) (h1)
  have v1 := p576 (M := M) (a0) (a1) (a2) ((show (M → Prop) from (t120 (a3)))) ((show (M → Prop) from (t120 (a4)))) (h0) (v0)
  exact v1
-- Actual MMB 2019 elneq2d
theorem p2019 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (t0 (a0) (t10 (M := M) (a2) (a3)))) : (t0 (a0) (t3 (t16 (M := M) (a1) (t120 (a2))) (t16 (M := M) (a1) (t120 (a3))))) := by
  have v0 := p354 (M := M) (a0) (a1)
  have v1 := p2018 (M := M) (a0) (a1) (a1) (a2) (a3) (v0) (h0)
  exact v1
-- Actual MMB 2020 elneq2
theorem p2020 (a0 : M) (a1 : M) (a2 : M)  : (t0 (t10 (M := M) (a1) (a2)) (t3 (t16 (M := M) (a0) (t120 (a1))) (t16 (M := M) (a0) (t120 (a2))))) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  have v0 := p8 (e0)
  have v1 := p2019 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 2021 elneq
theorem p2022 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) : (t0 (a0) (t10 (M := M) (t84 (M := M) (t120 (a1)) (a3)) (t84 (M := M) (t120 (a2)) (a3)))) := by
  have v0 := p2015 (M := M) (a0) (a1) (a2) (h0)
  have v1 := p1477 (M := M) (a0) ((show (M → Prop) from (t120 (a1)))) ((show (M → Prop) from (t120 (a2)))) (a3) (v0)
  exact v1
-- Actual MMB 2023 appneq1
theorem p2025 (a0 : M)  : (t3 (t16 (M := M) (t28 (M := M)) (t120 (a0))) (t62 (M := M) (a0))) := by
  let e0  : M := (t28 (M := M))
  let e3  : M := (t119 (M := M) (a0) (e0))
  have v0 := p149 ((show Prop from (t16 (M := M) (e0) ((show (M → Prop) from (t120 (a0))))))) ((show Prop from (t62 (M := M) (e3)))) ((show Prop from (t62 (M := M) (a0))))
  have v1 := p2017 (M := M) (e0) (a0)
  have v2 := ((v0) (v1))
  have v3 := p1188 (M := M) (e3) (a0)
  have v4 := p2003 (M := M) (a0)
  have v5 := ((v3) (v4))
  have v6 := ((v2) (v5))
  exact v6
-- Actual MMB 2026 elshr
theorem p2026 (a0 : M) (a1 : M) (a2 : M)  : (t3 (t16 (M := M) (a0) (t120 (t119 (M := M) (a1) (a2)))) (t16 (M := M) (t44 (M := M) (a0) (a2)) (t120 (a1)))) := by
  let e0  : M := (t119 (M := M) (a1) (a2))
  let e3  : M := (t119 (M := M) (e0) (a0))
  let e4  : Prop := (t62 (M := M) (e3))
  let e5  : M := (t44 (M := M) (a0) (a2))
  let e7  : Prop := (t16 (M := M) (e5) ((show (M → Prop) from (t120 (a1)))))
  let e12  : M := (t119 (M := M) (a1) (e5))
  let e14  : M := (t44 (M := M) (a2) (a0))
  have v0 := p149 ((show Prop from (t16 (M := M) (a0) ((show (M → Prop) from (t120 (e0))))))) (e4) (e7)
  have v1 := p2017 (M := M) (a0) (e0)
  have v2 := ((v0) (v1))
  have v3 := p152 (e4) ((show Prop from (t62 (M := M) (e12)))) (e7)
  have v4 := p1188 (M := M) (e3) (e12)
  have v5 := p342 (M := M) (e3) ((show M from (t119 (M := M) (a1) (e14)))) (e12)
  have v6 := p2005 (M := M) (a1) (a2) (a0)
  have v7 := ((v5) (v6))
  have v8 := p1993 (M := M) (a1) (e14) (e5)
  have v9 := p816 (M := M) (a2) (a0)
  have v10 := ((v8) (v9))
  have v11 := ((v7) (v10))
  have v12 := ((v4) (v11))
  have v13 := ((v3) (v12))
  have v14 := p2017 (M := M) (e5) (a1)
  have v15 := ((v13) (v14))
  have v16 := ((v2) (v15))
  exact v16
-- Actual MMB 2027 elshl
theorem p2027 (a0 : M) (a1 : M) (a2 : M)  : (t3 (t16 (M := M) (a0) (t120 (t118 (M := M) (a1) (a2)))) (t2 (t47 (M := M) (a2) (a0)) (t16 (M := M) (t46 (M := M) (a0) (a2)) (t120 (a1))))) := by
  let e0  : M := (t118 (M := M) (a1) (a2))
  let e3  : M := (t119 (M := M) (e0) (a0))
  let e4  : Prop := (t62 (M := M) (e3))
  let e5  : Prop := (t47 (M := M) (a2) (a0))
  let e6  : M := (t46 (M := M) (a0) (a2))
  let e8  : Prop := (t16 (M := M) (e6) ((show (M → Prop) from (t120 (a1)))))
  let e9  : Prop := (t2 (e5) (e8))
  let e14  : M := (t31 (M := M))
  let e15  : Prop := (t58 (M := M) (e14) (e3))
  let e16  : Prop := (t48 (M := M) (a0) (a2))
  let e18  : M := (t46 (M := M) (a2) (a0))
  let e19  : M := (t118 (M := M) (a1) (e18))
  let e23  : Prop := (t58 (M := M) (e14) (e19))
  let e28  : M := (t119 (M := M) (a1) (e6))
  have v0 := p149 ((show Prop from (t16 (M := M) (a0) ((show (M → Prop) from (t120 (e0))))))) (e4) (e9)
  have v1 := p2017 (M := M) (a0) (e0)
  have v2 := ((v0) (v1))
  have v3 := p1199 (M := M) (e3)
  have v4 := p41 (e5) (e15)
  have v5 := p931 (M := M) (a0) (a2)
  have v6 := p894 (M := M) (a0) (a2)
  have v7 := p2012 (M := M) (a1) (a2) (a0)
  have v8 := p11 (e16) ((show Prop from (t47 (M := M) (a0) (a2)))) ((show Prop from (t10 (M := M) (e3) (e19)))) (v6) (v7)
  have v9 := p1122 (M := M) (e16) (e14) (e3) (e19) (v8)
  have v10 := p940 (M := M) (a0) (a2)
  have v11 := p2001 (M := M) (a1) (e18)
  have v12 := p155 (e16) ((show Prop from (t48 (M := M) ((show M from (t28 (M := M)))) (e18)))) (e23) (v10) (v11)
  have v13 := p120 (e16) (e23) (e15) (v9) (v12)
  have v14 := p156 ((show Prop from (t1 (e5)))) (e16) (e15) (v5) (v13)
  have v15 := ((v4) (v14))
  have v16 := p155 (e4) ((show Prop from (t1 (e15)))) (e5) (v3) (v15)
  have v17 := p53 (e5) (e8)
  have v18 := p2017 (M := M) (e6) (a1)
  have v19 := p2013 (M := M) (a1) (a2) (a0)
  have v20 := p1187 (M := M) (e5) (e3) (e28) (v19)
  have v21 := p160 (e5) (e4) ((show Prop from (t62 (M := M) (e28)))) (e8) (v18) (v20)
  have v22 := p181 (e5) (e8)
  have v23 := p148 (e5) (e4) (e8) (e9) (v21) (v22)
  have v24 := p232 (e5) (e4) (e9) (v16) (v17) (v23)
  have v25 := ((v2) (v24))
  exact v25
-- Actual MMB 2028 elmodpow2
theorem p2031 (a0 : M) (a1 : M)  : (t3 (t16 (M := M) (a0) (t120 (t56 (M := M) (a1) (t31 (M := M))))) (t16 (M := M) (t29 (M := M) (a0)) (t120 (a1)))) := by
  let e1  : M := (t56 (M := M) (a1) ((show M from (t31 (M := M)))))
  let e4  : M := (t30 (M := M))
  let e5  : M := (t119 (M := M) (a1) (e4))
  let e7  : Prop := (t16 (M := M) (a0) ((show (M → Prop) from (t120 (e5)))))
  let e8  : M := (t29 (M := M) (a0))
  let e9  : (M → Prop) := (t120 (a1))
  let e10  : Prop := (t16 (M := M) (e8) (e9))
  let e16  : M := (t44 (M := M) (a0) (e4))
  have v0 := p151 ((show Prop from (t16 (M := M) (a0) ((show (M → Prop) from (t120 (e1))))))) (e7) (e10)
  have v1 := p2020 (M := M) (a0) (e5) (e1)
  have v2 := p2004 (M := M) (a1)
  have v3 := ((v1) (v2))
  have v4 := ((v0) (v3))
  have v5 := p149 (e7) ((show Prop from (t16 (M := M) (e16) (e9)))) (e10)
  have v6 := p2026 (M := M) (a0) (a1) (e4)
  have v7 := ((v5) (v6))
  have v8 := p572 (M := M) (e9) (e16) (e8)
  have v9 := p813 (M := M) (a0)
  have v10 := ((v8) (v9))
  have v11 := ((v7) (v10))
  have v12 := ((v4) (v11))
  exact v12
-- Actual MMB 2032 elb0

end ZF207.MM0ModelReplay
