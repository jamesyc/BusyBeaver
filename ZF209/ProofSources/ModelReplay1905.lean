module
public import ModelReplay1904
public import ModelLiteralRecursionCertificate
public import ModelLiteralConditionalCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 1905 recS
theorem p1905 (e : Nat → M) (a0 : M) (a1 : (M → Prop)) (a2 : M) (predicate : ZF209.MM0ModelPeano.FormulaCertificate e 1 (fun v => a1 (v 0))) : (t10 (M := M) (t110 (M := M) (a0) (a1) (t29 (M := M) (a2))) (t84 (M := M) (a1) (t110 (M := M) (a0) (a1) (a2)))) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e1 (u0 : M) : M := (t29 (M := M) u0)
  let e2  : M := (t29 (M := M) (a2))
  let e3 (u0 : M) : M := (t110 (M := M) (a0) (a1) u0)
  let e4  : M := (t110 (M := M) (a0) (a1) (a2))
  let e5 (u0 : M) : M := (t110 (M := M) (a0) (a1) (e1 u0))
  let e6  : M := (t110 (M := M) (a0) (a1) (e2))
  let e7 (u0 : M) : M := (t84 (M := M) (a1) (e3 u0))
  let e8  : M := (t84 (M := M) (a1) (e4))
  let e9 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e10 (u0 : M) : M := (t29 (M := M) u0)
  let e11 (u0 : M) : M := (t110 (M := M) (a0) (a1) u0)
  let e12 (u0 : M) : M := (t110 (M := M) (a0) (a1) (e10 u0))
  let e13 (u0 : M) : M := (t84 (M := M) (a1) (e11 u0))
  let e14 (u0 : M) (u1 : M) : Prop := (t47 (M := M) u1 (e10 u0))
  let e15 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 (e10 u0))
  let e16 (u0 : M) : M := (t110 (M := M) (a0) (a1) u0)
  let e17 (u0 : M) (u1 : M) : M := (t50 (M := M) (e15 u0 u1) (e13 u0) (e16 u1))
  let e18 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e14 u0 x0_0)))
  let e19 (u0 : M) : Prop := (t49 (M := M) (e18 u0))
  let e20 (u0 : M) : (M → Prop) := (t109 (M := M) u0)
  let e21 (u0 : M) (u1 : M) : M := (t84 (M := M) (e20 u0) u1)
  let e22 (u0 : M) (u1 : M) (u2 : M) : Prop := (t10 (M := M) (e21 u1 u2) (e17 u0 u2))
  let e23 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e14 u0 u2) (e22 u0 u1 u2))
  let e24 (u0 : M) (u1 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e23 u0 u1 x0_0)))
  let e25 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (e24 u0 x0_0)))
  let e26  : M := (t28 (M := M))
  let e27 (u0 : M) : Prop := (t10 (M := M) u0 (e26))
  let e28 (u0 : M) : Prop := (t1 (e27 u0))
  let e29 (u0 : M) (u1 : M) : Prop := (t0 (e15 u0 u1) (e28 u1))
  let e30 (u0 : M) (u1 : M) : Prop := (t1 (e15 u0 u1))
  let e31 (u0 : M) (u1 : M) : Prop := (t0 (e27 u1) (e30 u0 u1))
  let e32 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e17 u0 u1) (e16 u1))
  let e33  : M := (t110 (M := M) (a0) (a1) (e26))
  let e34 (u0 : M) : M := (t84 (M := M) (e20 u0) (e26))
  let e35 (u0 : M) : Prop := (t47 (M := M) (e26) (e10 u0))
  let e36 (u0 : M) : Prop := (t10 (M := M) (e34 u0) (e33))
  let e37 (u0 : M) (u1 : M) : Prop := (t0 (e35 u0) (e36 u1))
  let e38 (u0 : M) (u1 : M) : Prop := (t48 (M := M) u0 u1)
  let e39 (u0 : M) : Prop := (t10 (M := M) (e5 u0) (e7 u0))
  let e40 (u0 : M) (u1 : M) : Prop := (t0 (e38 u0 u1) (e39 u0))
  let e41 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e40 x0_0 u0)))
  let e42 (u0 : M) : Prop := (t10 (M := M) (e34 u0) (a0))
  let e43 (u0 : M) (u1 : M) : M := (t84 (M := M) (e20 u1) (e10 u0))
  let e44 (u0 : M) : Prop := (t47 (M := M) (e10 u0) (e10 u0))
  let e45 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e43 u0 u1) (e13 u0))
  let e46 (u0 : M) (u1 : M) : Prop := (t0 (e44 u0) (e45 u0 u1))
  let e47 (u0 : M) (u1 : M) : Prop := (t2 (e41 u0) (e24 u0 u1))
  let e48 (u0 : M) (u1 : M) : Prop := (t47 (M := M) u1 u0)
  let e49 (u0 : M) (u1 : M) (u2 : M) : Prop := (t2 (e47 u0 u1) (e48 u0 u2))
  let e50 (u0 : M) : M := (t29 (M := M) u0)
  let e51 (u0 : M) (u1 : M) : Prop := (t47 (M := M) (e50 u1) (e10 u0))
  let e52 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (e50 u1))
  let e53 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e50 u1) (e10 u0))
  let e54 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e55 (u0 : M) : M := (t110 (M := M) (a0) (a1) (e50 u0))
  let e56 (u0 : M) (u1 : M) : M := (t84 (M := M) (e20 u0) (e50 u1))
  let e57 (u0 : M) (u1 : M) : M := (t50 (M := M) (e54 u0 u1) (e13 u0) (e55 u1))
  let e58 (u0 : M) (u1 : M) (u2 : M) : Prop := (t10 (M := M) (e56 u1 u2) (e57 u0 u2))
  let e59 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e51 u0 u2) (e58 u0 u1 u2))
  let e60 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e57 u0 u1) (e13 u0))
  let e61 (u0 : M) (u1 : M) : M := (t84 (M := M) (e20 u0) u1)
  let e62 (u0 : M) : M := (t110 (M := M) (a0) (a1) u0)
  let e63 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e64 (u0 : M) (u1 : M) : Prop := (t47 (M := M) u1 (e10 u0))
  let e65 (u0 : M) (u1 : M) (u2 : M) : Prop := (t3 (e14 u0 u1) (e64 u0 u2))
  let e66 (u0 : M) (u1 : M) (u2 : M) : Prop := (t2 (e48 u0 u2) (e63 u1 u2))
  let e67 (u0 : M) : Prop := (t47 (M := M) u0 (e10 u0))
  let e68 (u0 : M) (u1 : M) (u2 : M) : Prop := (t3 (e23 u0 u1 u2) (e22 u0 u1 u2))
  let e69 (u0 : M) (u1 : M) (u2 : M) : Prop := (t10 (M := M) (e21 u0 u1) (e61 u0 u2))
  let e70 (u0 : M) (u1 : M) : Prop := (t48 (M := M) u1 (e10 u0))
  let e71 (u0 : M) (u1 : M) : Prop := (t0 (e70 u0 u1) (e30 u0 u1))
  let e72 (u0 : M) (u1 : M) : Prop := (t47 (M := M) u1 u0)
  let e73 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e16 u0) (e62 u1))
  let e74 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e61 u0 u1) (e62 u1))
  let e75 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e62 u1) (e61 u0 u1))
  let e76 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e24 u0 u1) (e75 u1 u2))
  let e77 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e62 u1) (e11 u0))
  let e78 (u0 : M) (u1 : M) (u2 : M) : Prop := (t2 (e49 u0 u1 u2) (e54 u0 u2))
  let e79 (u0 : M) (u1 : M) : M := (t84 (M := M) (a1) (e61 u0 u1))
  let e80 (u0 : M) (u1 : M) : Prop := (t1 (e54 u0 u1))
  let e81 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e57 u0 u1) (e55 u1))
  let e82 (u0 : M) (u1 : M) : Prop := (t48 (M := M) u1 u0)
  let e83 (u0 : M) (u1 : M) : Prop := (t4 (e82 u0 u1) (e54 u0 u1))
  let e84 (u0 : M) (u1 : M) : Prop := (t0 (e80 u0 u1) (e82 u0 u1))
  let e85 (u0 : M) (u1 : M) : Prop := (t0 (e83 u0 u1) (e84 u0 u1))
  let e86 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e87 (u0 : M) : M := (t84 (M := M) (a1) (e62 u0))
  let e88 (u0 : M) : Prop := (t10 (M := M) (e55 u0) (e87 u0))
  let e89 (u0 : M) (u1 : M) : Prop := (t0 (e82 u0 u1) (e88 u1))
  let e90 (u0 : M) (u1 : M) (u2 : M) : Prop := (t2 (e49 u0 u1 u2) (e80 u0 u2))
  let e91 (u0 : M) (u1 : M) (u2 : M) : Prop := (t10 (M := M) (e57 u0 u2) (e79 u1 u2))
  let e92 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e56 u0 u1) (e79 u0 u1))
  let e93 (u0 : M) (u1 : M) : Prop := (t48 (M := M) u1 (e10 u0))
  let e94 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e93 u0 u2) (e92 u1 u2))
  let e95 (u0 : M) : Prop := (t10 (M := M) (e12 u0) (e13 u0))
  let e96  : Prop := (t6)
  let e97  : Prop := (t10 (M := M) (e6) (e8))
  let ee : Nat → M := fun i => Nat.casesOn i a0 e
  let recGraph : ZF209.MM0ModelPeano.FunctionGraphCertificate ee 1 (fun v => t110 (M := M) a0 a1 (v 0)) :=
    literalRecursion_certificate (predicate.prependParameter a0)
  let appGraph := literalApply_certificate (predicate.prependParameter a0)
  let stepCertificate : ZF209.MM0ModelPeano.FormulaCertificate ee 1 (fun v => e39 (v 0)) := {
    formula := (recGraph.precomposeSucc.equal (appGraph.compose (G := fun x => t110 (M := M) a0 a1 x) recGraph)).formula
    correct := by
      intro v
      exact (recGraph.precomposeSucc.equal (appGraph.compose (G := fun x => t110 (M := M) a0 a1 x) recGraph)).correct v
  }
  let trueCertificate : ZF209.MM0ModelPeano.FormulaCertificate ee 1 (fun _ => e96) := {
    formula := “0=0”
    correct := by intro v; simp [e96,t6]
  }
  let ep (n : M) : Nat → M := fun i => Nat.casesOn i (e13 n) (fun i => Nat.casesOn i n ee)
  let domainCertificate (n : M) : ZF209.MM0ModelPeano.FormulaCertificate (ep n) 1 (fun v => e14 n (v 0)) := {
    formula := “x. ∃q, x+q=&1+1”
    correct := by
      intro v
      classical
      simp [e14,e10,t47,t9,t1,t8,t10,t44,ep,t29]
  }
  let conditionCertificate (n : M) : ZF209.MM0ModelPeano.FormulaCertificate (ep n) 1 (fun v => e15 n (v 0)) := {
    formula := “x. x=&1+1”
    correct := by intro v; rfl
  }
  let constantGraph (n : M) : ZF209.MM0ModelPeano.FunctionGraphCertificate (ep n) 1 (fun _ => e13 n) := {
    formula := “y x. y=&0”
    correct := by intro v y; rfl
  }
  let branchGraph (n : M) : ZF209.MM0ModelPeano.FunctionGraphCertificate (ep n) 1 (fun v => e17 n (v 0)) :=
    literalConditional_certificate (P := fun x => e15 n x) (F := fun _ => e13 n) (G := fun x => t110 (M := M) a0 a1 x)
      (conditionCertificate n) (constantGraph n) ((recGraph.prependParameter n).prependParameter (e13 n))
  have v0 := fun z0 : M => p739 (M := M) z0 (a2)
  have v1 := fun z0 : M => p1901 (M := M) (e0 z0) (a0) (a1) (e1 z0) (e2) (v0 z0)
  have v2 := fun z0 : M => p1902 (M := M) (a0) (a1) z0 (a2)
  have v3 := fun z0 : M => p1479 (M := M) (e0 z0) (a1) (e3 z0) (e4) (v2 z0)
  have v4 := fun z0 : M => p350 (M := M) (e0 z0) (e5 z0) (e6) (e7 z0) (e8) (v1 z0) (v3 z0)
  have v5 := fun z0 : M => fun z1 : M => p739 (M := M) z0 z1
  have v6 := fun z0 : M => fun z1 : M => p1901 (M := M) (e9 z0 z1) (a0) (a1) (e1 z0) (e10 z1) (v5 z0 z1)
  have v7 := fun z0 : M => fun z1 : M => p1902 (M := M) (a0) (a1) z0 z1
  have v8 := fun z0 : M => fun z1 : M => p1479 (M := M) (e9 z0 z1) (a1) (e3 z0) (e11 z1) (v7 z0 z1)
  have v9 := fun z0 : M => fun z1 : M => p350 (M := M) (e9 z0 z1) (e5 z0) (e12 z1) (e7 z0) (e13 z1) (v6 z0 z1) (v8 z0 z1)
  have v10 := fun z0 : M => p1894 (M := M) (ep z0) (fun w1 : M => (e14 z0 w1)) (fun w1 : M => (e17 z0 w1)) (domainCertificate z0) (branchGraph z0)
  have v11 := fun z0 : M => p974 (M := M) (e10 z0)
  have v12 := fun z0 : M => b3 (e19 z0) (e25 z0) (v10 z0) (v11 z0)
  have v13 := p1904 (M := M) (a0) (a1)
  have v14 := fun z0 : M => p868 (M := M) (e10 z0)
  have v15 := fun z0 : M => fun z1 : M => p853 (M := M) z1 (e26) (e10 z0)
  have v16 := fun z0 : M => fun z1 : M => p1480 (M := M) (e20 z0) z1 (e26)
  have v17 := fun z0 : M => fun z1 : M => p987 (M := M) (e15 z0 z1) (e13 z0) (e16 z1)
  have v18 := fun z0 : M => fun z1 : M => p38 (e15 z0 z1) (e27 z1)
  have v19 := fun z0 : M => fun z1 : M => p743 (M := M) z1 z0
  have v20 : (∀ z0 : M, (∀ z1 : M, (e29 z0 z1))) := (show (∀ z0 : M, (∀ z1 : M, (e29 z0 z1))) from v19)
  have v21 := fun z0 : M => fun z1 : M => b3 (e29 z0 z1) (e31 z0 z1) (v18 z0 z1) (v20 z0 z1)
  have v22 := fun z0 : M => fun z1 : M => p10 (e27 z1) (e30 z0 z1) (e32 z0 z1) (v17 z0 z1) (v21 z0 z1)
  have v23 := fun z0 : M => p1902 (M := M) (a0) (a1) z0 (e26)
  have v24 := fun z0 : M => fun z1 : M => p357 (M := M) (e27 z1) (e17 z0 z1) (e16 z1) (e33) (v22 z0 z1) (v23 z1)
  have v25 := fun z0 : M => fun z1 : M => fun z2 : M => p350 (M := M) (e27 z2) (e21 z1 z2) (e34 z1) (e17 z0 z2) (e33) (v16 z1 z2) (v24 z0 z2)
  have v26 := fun z0 : M => fun z1 : M => fun z2 : M => p188 (e27 z2) (e14 z0 z2) (e35 z0) (e22 z0 z1 z2) (e36 z1) (v15 z0 z2) (v25 z0 z1 z2)
  have v27 := fun z0 : M => fun z1 : M => p440 (M := M) (e26) (fun w0 : M => (e23 z0 z1 w0)) (e37 z0 z1) ((fun w0 : M => v26 z0 z1 w0))
  have v28 := fun z0 : M => fun z1 : M => p7 (e24 z0 z1) (e35 z0) (e36 z1) (v14 z0) (v27 z0 z1)
  have v29 := fun z0 : M => fun z1 : M => p362 (M := M) (e24 z0 z1) (e34 z1) (e33) (a0) (v13) (v28 z0 z1)
  have v30 := fun z0 : M => fun z1 : M => p63 (e41 z0) (e24 z0 z1) (e42 z1) (v29 z0 z1)
  have v31 := fun z0 : M => p857 (M := M) (e10 z0)
  have v32 := fun z0 : M => fun z1 : M => p853 (M := M) z1 (e10 z0) (e10 z0)
  have v33 := fun z0 : M => fun z1 : M => fun z2 : M => p1480 (M := M) (e20 z1) z2 (e10 z0)
  have v34 := fun z0 : M => fun z1 : M => p986 (M := M) (e15 z0 z1) (e13 z0) (e16 z1)
  have v35 := fun z0 : M => fun z1 : M => fun z2 : M => p350 (M := M) (e15 z0 z2) (e21 z1 z2) (e43 z0 z1) (e17 z0 z2) (e13 z0) (v33 z0 z1 z2) (v34 z0 z2)
  have v36 := fun z0 : M => fun z1 : M => fun z2 : M => p188 (e15 z0 z2) (e14 z0 z2) (e44 z0) (e22 z0 z1 z2) (e45 z0 z1) (v32 z0 z2) (v35 z0 z1 z2)
  have v37 := fun z0 : M => fun z1 : M => p440 (M := M) (e10 z0) (fun w0 : M => (e23 z0 z1 w0)) (e46 z0 z1) ((fun w0 : M => v36 z0 z1 w0))
  have v38 := fun z0 : M => fun z1 : M => p7 (e24 z0 z1) (e44 z0) (e45 z0 z1) (v31 z0) (v37 z0 z1)
  have v39 := fun z0 : M => fun z1 : M => p63 (e41 z0) (e24 z0 z1) (e45 z0 z1) (v38 z0 z1)
  have v40 := fun z0 : M => fun z1 : M => p910 (M := M) z1 z0
  have v41 := fun z0 : M => fun z1 : M => p871 (M := M) z1 z0
  have v42 := fun z0 : M => fun z1 : M => fun z2 : M => p54 (e47 z0 z1) (e48 z0 z2)
  have v43 := fun z0 : M => fun z1 : M => fun z2 : M => p153 (e49 z0 z1 z2) (e48 z0 z2) (e51 z0 z2) (v41 z0 z2) (v42 z0 z1 z2)
  have v44 := fun z0 : M => fun z1 : M => fun z2 : M => p65 (e41 z0) (e24 z0 z1) (e48 z0 z2)
  have v45 := fun z0 : M => fun z1 : M => fun z2 : M => p853 (M := M) z1 (e50 z2) (e10 z0)
  have v46 := fun z0 : M => fun z1 : M => fun z2 : M => p1480 (M := M) (e20 z0) z1 (e50 z2)
  have v47 := fun z0 : M => fun z1 : M => b735 (M := M) z1 z0
  have v48 := fun z0 : M => fun z1 : M => fun z2 : M => p346 (M := M) z1 (e50 z2) (e10 z0)
  have v49 := fun z0 : M => fun z1 : M => fun z2 : M => p159 (e52 z1 z2) (e15 z0 z1) (e53 z0 z2) (e54 z0 z2) (v47 z0 z2) (v48 z0 z1 z2)
  have v50 := fun z0 : M => fun z1 : M => fun z2 : M => p354 (M := M) (e52 z1 z2) (e13 z0)
  have v51 := fun z0 : M => fun z1 : M => p1902 (M := M) (a0) (a1) z0 (e50 z1)
  have v52 := fun z0 : M => fun z1 : M => fun z2 : M => p978 (M := M) (e52 z1 z2) (e15 z0 z1) (e54 z0 z2) (e13 z0) (e13 z0) (e16 z1) (e55 z2) (v49 z0 z1 z2) (v50 z0 z1 z2) (v51 z1 z2)
  have v53 := fun z0 : M => fun z1 : M => fun z2 : M => fun z3 : M => p350 (M := M) (e52 z2 z3) (e21 z1 z2) (e56 z1 z3) (e17 z0 z2) (e57 z0 z3) (v46 z1 z2 z3) (v52 z0 z2 z3)
  have v54 := fun z0 : M => fun z1 : M => fun z2 : M => fun z3 : M => p188 (e52 z2 z3) (e14 z0 z2) (e51 z0 z3) (e22 z0 z1 z2) (e58 z0 z1 z3) (v45 z0 z2 z3) (v53 z0 z1 z2 z3)
  have v55 := fun z0 : M => fun z1 : M => fun z2 : M => p440 (M := M) (e50 z2) (fun w0 : M => (e23 z0 z1 w0)) (e59 z0 z1 z2) ((fun w0 : M => v54 z0 z1 w0 z2))
  have v56 := fun z0 : M => fun z1 : M => fun z2 : M => p11 (e49 z0 z1 z2) (e24 z0 z1) (e59 z0 z1 z2) (v44 z0 z1 z2) (v55 z0 z1 z2)
  have v57 := fun z0 : M => fun z1 : M => fun z2 : M => p6 (e49 z0 z1 z2) (e51 z0 z2) (e58 z0 z1 z2) (v43 z0 z1 z2) (v56 z0 z1 z2)
  have v58 := fun z0 : M => fun z1 : M => p986 (M := M) (e54 z0 z1) (e13 z0) (e55 z1)
  have v59 := fun z0 : M => fun z1 : M => fun z2 : M => p63 (e49 z0 z1 z2) (e54 z0 z2) (e60 z0 z2) (v58 z0 z2)
  have v60 := fun z0 : M => fun z1 : M => p341 (M := M) (e61 z0 z1) (e62 z1)
  have v61 := fun z0 : M => fun z1 : M => fun z2 : M => p287 (e14 z0 z2) (e22 z0 z1 z2)
  have v62 := fun z0 : M => fun z1 : M => fun z2 : M => p853 (M := M) z1 z2 (e10 z0)
  have v63 := fun z0 : M => fun z1 : M => fun z2 : M => p63 (e48 z0 z2) (e63 z1 z2) (e65 z0 z1 z2) (v62 z0 z1 z2)
  have v64 := fun z0 : M => fun z1 : M => fun z2 : M => p53 (e48 z0 z2) (e63 z1 z2)
  have v65 := fun z0 : M => p867 (M := M) z0
  have v66 := fun z0 : M => fun z1 : M => fun z2 : M => p4 (e66 z0 z1 z2) (e67 z0) (v65 z0)
  have v67 := fun z0 : M => fun z1 : M => fun z2 : M => p872 (M := M) (e66 z0 z1 z2) z2 z0 (e10 z0) (v64 z0 z1 z2) (v66 z0 z1 z2)
  have v68 := fun z0 : M => fun z1 : M => fun z2 : M => p120 (e66 z0 z1 z2) (e64 z0 z2) (e14 z0 z1) (v63 z0 z1 z2) (v67 z0 z1 z2)
  have v69 := fun z0 : M => fun z1 : M => fun z2 : M => fun z3 : M => p10 (e66 z0 z2 z3) (e14 z0 z2) (e68 z0 z1 z2) (v61 z0 z1 z2) (v68 z0 z2 z3)
  have v70 := fun z0 : M => fun z1 : M => fun z2 : M => p1480 (M := M) (e20 z0) z1 z2
  have v71 := fun z0 : M => fun z1 : M => fun z2 : M => fun z3 : M => p63 (e48 z0 z3) (e63 z2 z3) (e69 z1 z2 z3) (v70 z1 z2 z3)
  have v72 := fun z0 : M => fun z1 : M => p914 (M := M) z1 (e10 z0)
  have v73 : (∀ z0 : M, (∀ z1 : M, (e71 z0 z1))) := (show (∀ z0 : M, (∀ z1 : M, (e71 z0 z1))) from v72)
  have v74 := fun z0 : M => fun z1 : M => p910 (M := M) z1 z0
  have v75 := fun z0 : M => fun z1 : M => fun z2 : M => p853 (M := M) z1 z2 z0
  have v76 := fun z0 : M => fun z1 : M => p8 (e48 z0 z1)
  have v77 := fun z0 : M => fun z1 : M => fun z2 : M => p165 (e48 z0 z2) (e72 z0 z1) (e63 z1 z2) (e48 z0 z2) (v75 z0 z1 z2) (v76 z0 z2)
  have v78 := fun z0 : M => fun z1 : M => fun z2 : M => p83 (e48 z0 z2) (e63 z1 z2) (e72 z0 z1) (v77 z0 z1 z2)
  have v79 := fun z0 : M => fun z1 : M => fun z2 : M => p153 (e66 z0 z1 z2) (e72 z0 z1) (e70 z0 z1) (v74 z0 z1) (v78 z0 z1 z2)
  have v80 := fun z0 : M => fun z1 : M => fun z2 : M => p10 (e66 z0 z1 z2) (e70 z0 z1) (e30 z0 z1) (v73 z0 z1) (v79 z0 z1 z2)
  have v81 := fun z0 : M => fun z1 : M => fun z2 : M => p10 (e66 z0 z1 z2) (e30 z0 z1) (e32 z0 z1) (v17 z0 z1) (v80 z0 z1 z2)
  have v82 := fun z0 : M => fun z1 : M => p1902 (M := M) (a0) (a1) z0 z1
  have v83 := fun z0 : M => fun z1 : M => fun z2 : M => p63 (e48 z0 z2) (e63 z1 z2) (e73 z1 z2) (v82 z1 z2)
  have v84 := fun z0 : M => fun z1 : M => fun z2 : M => p357 (M := M) (e66 z0 z1 z2) (e17 z0 z1) (e16 z1) (e62 z2) (v81 z0 z1 z2) (v83 z0 z1 z2)
  have v85 := fun z0 : M => fun z1 : M => fun z2 : M => fun z3 : M => p350 (M := M) (e66 z0 z2 z3) (e21 z1 z2) (e61 z1 z3) (e17 z0 z2) (e62 z3) (v71 z0 z1 z2 z3) (v84 z0 z2 z3)
  have v86 := fun z0 : M => fun z1 : M => fun z2 : M => fun z3 : M => p145 (e66 z0 z2 z3) (e23 z0 z1 z2) (e22 z0 z1 z2) (e74 z1 z3) (v69 z0 z1 z2 z3) (v85 z0 z1 z2 z3)
  have v87 := fun z0 : M => fun z1 : M => fun z2 : M => fun z3 : M => p106 (e66 z0 z2 z3) (e23 z0 z1 z2) (e74 z1 z3) (v86 z0 z1 z2 z3)
  have v88 := fun z0 : M => fun z1 : M => fun z2 : M => fun z3 : M => p18 (e66 z0 z2 z3) (e23 z0 z1 z2) (e74 z1 z3) (e75 z1 z3) (v60 z1 z3) (v87 z0 z1 z2 z3)
  have v89 := fun z0 : M => fun z1 : M => fun z2 : M => p448 (M := M) (e75 z1 z2) (e48 z0 z2) z2 (fun w1 : M => (e23 z0 z1 w1)) ((fun w1 : M => v88 z0 z1 w1 z2))
  have v90 := fun z0 : M => fun z1 : M => fun z2 : M => p63 (e47 z0 z1) (e48 z0 z2) (e76 z0 z1 z2) (v89 z0 z1 z2)
  have v91 := fun z0 : M => fun z1 : M => fun z2 : M => p6 (e49 z0 z1 z2) (e24 z0 z1) (e75 z1 z2) (v44 z0 z1 z2) (v90 z0 z1 z2)
  have v92 := fun z0 : M => fun z1 : M => fun z2 : M => p62 (e49 z0 z1 z2) (e54 z0 z2) (e75 z1 z2) (v91 z0 z1 z2)
  have v93 := fun z0 : M => fun z1 : M => p1902 (M := M) (a0) (a1) z1 z0
  have v94 := fun z0 : M => fun z1 : M => fun z2 : M => p63 (e49 z0 z1 z2) (e54 z0 z2) (e77 z0 z2) (v93 z0 z2)
  have v95 := fun z0 : M => fun z1 : M => fun z2 : M => p353 (M := M) (e78 z0 z1 z2) (e61 z1 z2) (e62 z2) (e11 z0) (v92 z0 z1 z2) (v94 z0 z1 z2)
  have v96 := fun z0 : M => fun z1 : M => fun z2 : M => p1479 (M := M) (e78 z0 z1 z2) (a1) (e61 z1 z2) (e11 z0) (v95 z0 z1 z2)
  have v97 := fun z0 : M => fun z1 : M => fun z2 : M => p359 (M := M) (e78 z0 z1 z2) (e57 z0 z2) (e13 z0) (e79 z1 z2) (v59 z0 z1 z2) (v96 z0 z1 z2)
  have v98 := fun z0 : M => fun z1 : M => p987 (M := M) (e54 z0 z1) (e13 z0) (e55 z1)
  have v99 := fun z0 : M => fun z1 : M => fun z2 : M => p63 (e49 z0 z1 z2) (e80 z0 z2) (e81 z0 z2) (v98 z0 z2)
  have v100 := fun z0 : M => fun z1 : M => p266 (e82 z0 z1) (e54 z0 z1)
  have v101 : (∀ z0 : M, (∀ z1 : M, (e85 z0 z1))) := (show (∀ z0 : M, (∀ z1 : M, (e85 z0 z1))) from v100)
  have v102 := fun z0 : M => fun z1 : M => p926 (M := M) z1 z0
  have v103 := fun z0 : M => fun z1 : M => fun z2 : M => p153 (e49 z0 z1 z2) (e48 z0 z2) (e83 z0 z2) (v102 z0 z2) (v42 z0 z1 z2)
  have v104 := fun z0 : M => fun z1 : M => fun z2 : M => p10 (e49 z0 z1 z2) (e83 z0 z2) (e84 z0 z2) (v101 z0 z2) (v103 z0 z1 z2)
  have v105 := fun z0 : M => fun z1 : M => fun z2 : M => p83 (e49 z0 z1 z2) (e80 z0 z2) (e82 z0 z2) (v104 z0 z1 z2)
  have v106 := fun z0 : M => fun z1 : M => fun z2 : M => p75 (e41 z0) (e24 z0 z1) (e48 z0 z2) (e80 z0 z2)
  have v107 := fun z0 : M => fun z1 : M => fun z2 : M => p889 (M := M) z0 z2 z1
  have v108 := fun z0 : M => fun z1 : M => p739 (M := M) z0 z1
  have v109 := fun z0 : M => fun z1 : M => p1901 (M := M) (e86 z0 z1) (a0) (a1) (e1 z0) (e50 z1) (v108 z0 z1)
  have v110 := fun z0 : M => fun z1 : M => p1902 (M := M) (a0) (a1) z0 z1
  have v111 := fun z0 : M => fun z1 : M => p1479 (M := M) (e86 z0 z1) (a1) (e3 z0) (e62 z1) (v110 z0 z1)
  have v112 := fun z0 : M => fun z1 : M => p350 (M := M) (e86 z0 z1) (e5 z0) (e55 z1) (e7 z0) (e87 z1) (v109 z0 z1) (v111 z0 z1)
  have v113 := fun z0 : M => fun z1 : M => fun z2 : M => p188 (e86 z0 z2) (e38 z0 z1) (e82 z1 z2) (e39 z0) (e88 z2) (v107 z0 z1 z2) (v112 z0 z2)
  have v114 := fun z0 : M => fun z1 : M => p440 (M := M) z1 (fun w0 : M => (e40 w0 z0)) (e89 z0 z1) ((fun w0 : M => v113 w0 z0 z1))
  have v115 := fun z0 : M => fun z1 : M => fun z2 : M => p11 (e90 z0 z1 z2) (e41 z0) (e89 z0 z2) (v106 z0 z1 z2) (v114 z0 z2)
  have v116 := fun z0 : M => fun z1 : M => fun z2 : M => p6 (e90 z0 z1 z2) (e82 z0 z2) (e88 z2) (v105 z0 z1 z2) (v115 z0 z1 z2)
  have v117 := fun z0 : M => fun z1 : M => fun z2 : M => p62 (e49 z0 z1 z2) (e80 z0 z2) (e75 z1 z2) (v91 z0 z1 z2)
  have v118 := fun z0 : M => fun z1 : M => fun z2 : M => p1479 (M := M) (e90 z0 z1 z2) (a1) (e62 z2) (e61 z1 z2) (v117 z0 z1 z2)
  have v119 := fun z0 : M => fun z1 : M => fun z2 : M => p357 (M := M) (e90 z0 z1 z2) (e55 z2) (e87 z2) (e79 z1 z2) (v116 z0 z1 z2) (v118 z0 z1 z2)
  have v120 := fun z0 : M => fun z1 : M => fun z2 : M => p357 (M := M) (e90 z0 z1 z2) (e57 z0 z2) (e55 z2) (e79 z1 z2) (v99 z0 z1 z2) (v119 z0 z1 z2)
  have v121 := fun z0 : M => fun z1 : M => fun z2 : M => p99 (e49 z0 z1 z2) (e54 z0 z2) (e91 z0 z1 z2) (v97 z0 z1 z2) (v120 z0 z1 z2)
  have v122 := fun z0 : M => fun z1 : M => fun z2 : M => p357 (M := M) (e49 z0 z1 z2) (e56 z1 z2) (e57 z0 z2) (e79 z1 z2) (v57 z0 z1 z2) (v121 z0 z1 z2)
  have v123 := fun z0 : M => fun z1 : M => fun z2 : M => p84 (e47 z0 z1) (e48 z0 z2) (e92 z1 z2) (v122 z0 z1 z2)
  have v124 := fun z0 : M => fun z1 : M => fun z2 : M => p162 (e47 z0 z1) (e93 z0 z2) (e48 z0 z2) (e92 z1 z2) (v40 z0 z2) (v123 z0 z1 z2)
  have v125 := fun z0 : M => fun z1 : M => p338 (M := M) (e47 z0 z1) (fun w0 : M => (e94 z0 z1 w0)) ((fun w0 : M => v124 z0 z1 w0))
  have v126 := fun z0 : M => fun z1 : M => p1903 (M := M) (e47 z0 z1) (a1) z1 (e10 z0) (e13 z0) (a0) (v30 z0 z1) (v39 z0 z1) (v125 z0 z1)
  have v127 := fun z0 : M => p425 (M := M) (e41 z0) (fun w0 : M => (e24 z0 w0)) (e95 z0) ((fun w0 : M => v126 z0 w0))
  have v128 := fun z0 : M => p7 (e41 z0) (e25 z0) (e95 z0) (v12 z0) (v127 z0)
  have v129 := fun z0 : M => p63 (e96) (e41 z0) (e95 z0) (v128 z0)
  have v130 := p968 (M := M) ee (e96) (fun w2 : M => (a2)) (fun w1 : M => (e39 w1)) (fun w2 : M => (e97)) (fun w2 : M => (e95 w2)) trueCertificate stepCertificate ((fun w1 : M => (fun w2 : M => v4 w1))) ((fun w1 : M => (fun w2 : M => v9 w1 w2))) ((fun w2 : M => v129 w2)) 0
  have v131 := p318 (e97) (v130)
  exact v131

end ZF209.MM0ModelReplay
