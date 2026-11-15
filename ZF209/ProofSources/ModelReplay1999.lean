module
public import ModelReplay1976
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 1977 powdvd
theorem p1977 (a0 : M) (a1 : M) (a2 : M)  : (t0 (t47 (M := M) (a1) (a2)) (t58 (M := M) (t117 (M := M) (a0) (a1)) (t117 (M := M) (a0) (a2)))) := by
  let e0  : M := (t117 (M := M) (a0) (a1))
  let e1  : M := (t46 (M := M) (a2) (a1))
  let e2  : M := (t117 (M := M) (a0) (e1))
  let e3  : Prop := (t47 (M := M) (a1) (a2))
  let e4  : M := (t44 (M := M) (e1) (a1))
  let e5  : M := (t45 (M := M) (e2) (e0))
  let e7  : M := (t117 (M := M) (a0) (a2))
  have v0 := p1130 (M := M) (e0) (e2)
  have v1 := p1975 (M := M) (a0) (e1) (a1)
  have v2 := p861 (M := M) (a2) (a1)
  have v3 := p1963 (M := M) (e3) (a0) (e4) (a2) (v2)
  have v4 := p361 (M := M) (e3) (e5) ((show M from (t117 (M := M) (a0) (e4)))) (e7) (v1) (v3)
  have v5 := p1122 (M := M) (e3) (e0) (e5) (e7) (v4)
  have v6 := p121 (e3) ((show Prop from (t58 (M := M) (e0) (e5)))) ((show Prop from (t58 (M := M) (e0) (e7)))) (v0) (v5)
  exact v6
-- Actual MMB 1978 powdvd1
theorem p1978 (a0 : M) (a1 : M)  : (t0 (t48 (M := M) (t28 (M := M)) (a1)) (t58 (M := M) (a0) (t117 (M := M) (a0) (a1)))) := by
  let e1  : M := (t117 (M := M) (a0) ((show M from (t30 (M := M)))))
  let e2  : M := (t117 (M := M) (a0) (a1))
  let e4  : Prop := (t58 (M := M) (e1) (e2))
  let e7  : M := (t28 (M := M))
  let e9  : Prop := (t48 (M := M) (e7) (a1))
  let e10  : Prop := (t0 (e9) (e4))
  have v0 := p1121 (M := M) (e1) (a0) (e2)
  have v1 := p1968 (M := M) (a0)
  have v2 := ((v0) (v1))
  have v3 := p1977 (M := M) (a0) ((show M from (t29 (M := M) (e7)))) (a1)
  have v4 : (e10) := (show (e10) from v3)
  have v5 := p153 (e9) (e4) ((show Prop from (t58 (M := M) (a0) (e2)))) (v2) (v4)
  exact v5
-- Actual MMB 1979 lepow2a
theorem p1979 (a0 : M) (a1 : M) (a2 : M)  : (t0 (t13 (M := M) (a0) (t28 (M := M))) (t0 (t47 (M := M) (a1) (a2)) (t47 (M := M) (t117 (M := M) (a0) (a1)) (t117 (M := M) (a0) (a2))))) := by
  let e0  : M := (t28 (M := M))
  let e1  : Prop := (t13 (M := M) (a0) (e0))
  let e2  : Prop := (t47 (M := M) (a1) (a2))
  let e3  : M := (t117 (M := M) (a0) (a2))
  let e5  : M := (t117 (M := M) (a0) (a1))
  have v0 := p1972 (M := M) (a0) (a2)
  have v1 := p62 (e1) (e2) ((show Prop from (t13 (M := M) (e3) (e0)))) (v0)
  have v2 := p1977 (M := M) (a0) (a1) (a2)
  have v3 := p63 (e1) (e2) ((show Prop from (t58 (M := M) (e5) (e3)))) (v2)
  have v4 := p1139 (M := M) ((show Prop from (t2 (e1) (e2)))) (e5) (e3) (v1) (v3)
  have v5 := p84 (e1) (e2) ((show Prop from (t47 (M := M) (e5) (e3)))) (v4)
  exact v5
-- Actual MMB 1980 ltpow2
theorem p1982 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) (h1 : (t0 (a0) (t10 (M := M) (a3) (a4)))) : (t0 (a0) (t10 (M := M) (t118 (M := M) (a1) (a3)) (t118 (M := M) (a2) (a4)))) := by
  let e0  : M := (t31 (M := M))
  let e6  : Prop := (t0 (a0) ((show Prop from (t10 (M := M) ((show M from (t118 (M := M) (a1) (a3)))) ((show M from (t118 (M := M) (a2) (a4))))))))
  have v0 := p1963 (M := M) (a0) (e0) (a3) (a4) (h1)
  have v1 := p797 (M := M) (a0) (a1) (a2) ((show M from (t117 (M := M) (e0) (a3)))) ((show M from (t117 (M := M) (e0) (a4)))) (h0) (v0)
  have v2 : (e6) := (show (e6) from v1)
  exact v2
-- Actual MMB 1983 shleq
theorem p1986 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (t0 (a0) (t10 (M := M) (a2) (a3)))) : (t0 (a0) (t10 (M := M) (t118 (M := M) (a1) (a2)) (t118 (M := M) (a1) (a3)))) := by
  have v0 := p354 (M := M) (a0) (a1)
  have v1 := p1982 (M := M) (a0) (a1) (a1) (a2) (a3) (v0) (h0)
  exact v1
-- Actual MMB 1987 shleq2
theorem p1988 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) (h1 : (t0 (a0) (t10 (M := M) (a3) (a4)))) : (t0 (a0) (t10 (M := M) (t119 (M := M) (a1) (a3)) (t119 (M := M) (a2) (a4)))) := by
  let e0  : M := (t31 (M := M))
  let e6  : Prop := (t0 (a0) ((show Prop from (t10 (M := M) ((show M from (t119 (M := M) (a1) (a3)))) ((show M from (t119 (M := M) (a2) (a4))))))))
  have v0 := p1963 (M := M) (a0) (e0) (a3) (a4) (h1)
  have v1 := p1059 (M := M) (a0) (a1) (a2) ((show M from (t117 (M := M) (e0) (a3)))) ((show M from (t117 (M := M) (e0) (a4)))) (h0) (v0)
  have v2 : (e6) := (show (e6) from v1)
  exact v2
-- Actual MMB 1989 shreq
theorem p1990 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) : (t0 (a0) (t10 (M := M) (t119 (M := M) (a1) (a3)) (t119 (M := M) (a2) (a3)))) := by
  have v0 := p354 (M := M) (a0) (a3)
  have v1 := p1988 (M := M) (a0) (a1) (a2) (a3) (a3) (h0) (v0)
  exact v1
-- Actual MMB 1991 shreq1
theorem p1991 (a0 : M) (a1 : M) (a2 : M)  : (t0 (t10 (M := M) (a0) (a1)) (t10 (M := M) (t119 (M := M) (a0) (a2)) (t119 (M := M) (a1) (a2)))) := by
  let e0  : Prop := (t10 (M := M) (a0) (a1))
  have v0 := p8 (e0)
  have v1 := p1990 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 1992 shreq2d
theorem p1992 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (t0 (a0) (t10 (M := M) (a2) (a3)))) : (t0 (a0) (t10 (M := M) (t119 (M := M) (a1) (a2)) (t119 (M := M) (a1) (a3)))) := by
  have v0 := p354 (M := M) (a0) (a1)
  have v1 := p1988 (M := M) (a0) (a1) (a1) (a2) (a3) (v0) (h0)
  exact v1
-- Actual MMB 1993 shreq2
theorem p1993 (a0 : M) (a1 : M) (a2 : M)  : (t0 (t10 (M := M) (a1) (a2)) (t10 (M := M) (t119 (M := M) (a0) (a1)) (t119 (M := M) (a0) (a2)))) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  have v0 := p8 (e0)
  have v1 := p1992 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 1994 shl01
theorem p1996 (a0 : M)  : (t10 (M := M) (t118 (M := M) (t30 (M := M)) (a0)) (t117 (M := M) (t31 (M := M)) (a0))) := by
  let e1  : M := (t117 (M := M) ((show M from (t31 (M := M)))) (a0))
  let e4  : Prop := (t10 (M := M) ((show M from (t118 (M := M) ((show M from (t30 (M := M)))) (a0)))) (e1))
  have v0 := p829 (M := M) (e1)
  have v1 : (e4) := (show (e4) from v0)
  exact v1
-- Actual MMB 1997 shl12
theorem p1998 (a0 : M) (a1 : M) (a2 : M)  : (t10 (M := M) (t118 (M := M) (t118 (M := M) (a0) (a1)) (a2)) (t118 (M := M) (a0) (t44 (M := M) (a1) (a2)))) := by
  let e1  : M := (t118 (M := M) ((show M from (t118 (M := M) (a0) (a1)))) (a2))
  let e2  : M := (t31 (M := M))
  let e3  : M := (t117 (M := M) (e2) (a1))
  let e4  : M := (t117 (M := M) (e2) (a2))
  let e5  : M := (t45 (M := M) (e3) (e4))
  let e6  : M := (t45 (M := M) (a0) (e5))
  let e7  : M := (t44 (M := M) (a1) (a2))
  let e8  : M := (t118 (M := M) (a0) (e7))
  let e9  : Prop := (t10 (M := M) (e1) (e6))
  let e13  : M := (t117 (M := M) (e2) (e7))
  let e15  : Prop := (t0 ((show Prop from (t10 (M := M) (e13) (e5)))) ((show Prop from (t10 (M := M) (e8) (e6)))))
  have v0 := p344 (M := M) (e1) (e6) (e8)
  have v1 := p834 (M := M) (a0) (e3) (e4)
  have v2 : (e9) := (show (e9) from v1)
  have v3 := ((v0) (v2))
  have v4 := p805 (M := M) (a0) (e13) (e5)
  have v5 : (e15) := (show (e15) from v4)
  have v6 := p1975 (M := M) (e2) (a1) (a2)
  have v7 := ((v5) (v6))
  have v8 := ((v3) (v7))
  exact v8
-- Actual MMB 1999 shladd

end ZF209.MM0ModelReplay
