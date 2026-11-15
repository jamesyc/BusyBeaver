module
public import ModelReplay742
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def t40 := ZF209.MM0ModelPeano.the (M := M)
def t44 := (fun x y : M => x+y)
def t45 := (fun x y : M => x*y)
noncomputable def t43 (a0 : M) (a2 : M → M)  : M := (t40 (M := M) (t15 (M := M) (fun x1_0 : M => (t14 (M := M) (a0) (fun x2_1 : M => (t10 (M := M) x1_0 (a2 x2_1)))))))
noncomputable def t46 (a0 : M) (a1 : M)  : M := (t40 (M := M) (t15 (M := M) (fun x1_0 : M => (t10 (M := M) (t44 (M := M) (a1) x1_0) (a0)))))
noncomputable def t47 (a0 : M) (a1 : M)  : Prop := (t9 (M := M) (fun x0_0 : M => (t10 (M := M) (t44 (M := M) (a0) x0_0) (a1))))
noncomputable def t48 (a0 : M) (a1 : M)  : Prop := (t47 (M := M) (t29 (M := M) (a0)) (a1))
noncomputable def t49 (a0 : (M → Prop))  : Prop := (t9 (M := M) (fun x0_0 : M => (t8 (M := M) (fun x1_0 : M => (t0 (t16 (M := M) x1_0 (a0)) (t48 (M := M) x1_0 x0_0))))))
noncomputable def t50 (a0 : Prop) (a1 : M) (a2 : M)  : M := (t40 (M := M) (t15 (M := M) (fun x1_0 : M => (t5 (a0) (t10 (M := M) x1_0 (a1)) (t10 (M := M) x1_0 (a2))))))
noncomputable def t51 (a0 : M)  : Prop := (t13 (M := M) (a0) (t28 (M := M)))
noncomputable def t52 (a0 : M)  : Prop := (t48 (M := M) (a0) (t31 (M := M)))
noncomputable def t53 (a0 : Prop)  : M := (t50 (M := M) (a0) (t30 (M := M)) (t28 (M := M)))
noncomputable def t54 (a0 : M) (a1 : M)  : M := (t50 (M := M) (t48 (M := M) (a0) (a1)) (a0) (a1))
noncomputable def t55 (a0 : M) (a1 : M)  : M := (t50 (M := M) (t48 (M := M) (a0) (a1)) (a1) (a0))
noncomputable def t56 (a0 : M) (a1 : M)  : M := (t40 (M := M) (t15 (M := M) (fun x1_0 : M => (t9 (M := M) (fun x2_0 : M => (t2 (t48 (M := M) x2_0 (a1)) (t10 (M := M) (t44 (M := M) (t45 (M := M) (a1) x1_0) x2_0) (a0))))))))
noncomputable def t57 (a0 : M) (a1 : M)  : M := (t46 (M := M) (a0) (t45 (M := M) (a1) (t56 (M := M) (a0) (a1))))
noncomputable def t58 (a0 : M) (a1 : M)  : Prop := (t9 (M := M) (fun x0_0 : M => (t10 (M := M) (t45 (M := M) x0_0 (a0)) (a1))))
noncomputable def t59 (a0 : M) (a1 : M) (a2 : M)  : Prop := (t10 (M := M) (t57 (M := M) (a1) (a0)) (t57 (M := M) (a2) (a0)))
noncomputable def t60 (a0 : M)  : M := (t44 (M := M) (a0) (a0))
noncomputable def t61 (a0 : M)  : M := (t29 (M := M) (t60 (M := M) (a0)))
noncomputable def t62 (a0 : M)  : Prop := (t10 (M := M) (t57 (M := M) (a0) (t31 (M := M))) (t30 (M := M)))
noncomputable def t63 (a0 : M) (a1 : M)  : M := (t44 (M := M) (t56 (M := M) (t45 (M := M) (t44 (M := M) (a0) (a1)) (t29 (M := M) (t44 (M := M) (a0) (a1)))) (t31 (M := M))) (a1))
noncomputable def t64 (a0 : M)  : M := (t40 (M := M) (t15 (M := M) (fun x1_0 : M => (t9 (M := M) (fun x2_0 : M => (t10 (M := M) (a0) (t63 (M := M) x1_0 x2_0)))))))
noncomputable def t65 (a0 : M)  : M := (t40 (M := M) (t15 (M := M) (fun x1_0 : M => (t9 (M := M) (fun x2_0 : M => (t10 (M := M) (a0) (t63 (M := M) x2_0 x1_0)))))))
noncomputable def t68 (a0 : M)  : M := (t64 (M := M) (t65 (M := M) (a0)))
noncomputable def t69 (a0 : M)  : M := (t65 (M := M) (t65 (M := M) (a0)))
noncomputable def t72 (a0 : (M → Prop))  : Prop := (t8 (M := M) (fun x0_0 : M => (t8 (M := M) (fun x1_0 : M => (t8 (M := M) (fun x2_0 : M => (t0 (t16 (M := M) (t63 (M := M) x0_0 x1_0) (a0)) (t0 (t16 (M := M) (t63 (M := M) x0_0 x2_0) (a0)) (t10 (M := M) x1_0 x2_0)))))))))
noncomputable def t73 (a1 : M → (M → Prop))  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (t16 (M := M) (t65 (M := M) x0_0) (t25 (M := M) (t64 (M := M) x0_0) (fun x2_1 : M => (a1 x2_1))))))
noncomputable def t74 (a1 : (M → Prop)) (a2 : M → (M → Prop))  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (t2 (t16 (M := M) (t64 (M := M) x0_0) (a1)) (t16 (M := M) (t65 (M := M) x0_0) (t25 (M := M) (t64 (M := M) x0_0) (fun x3_1 : M => (a2 x3_1)))))))
noncomputable def t75 (a0 : (M → Prop)) (a1 : (M → Prop))  : (M → Prop) := (t74 (M := M) (a0) (fun x0_0 : M => (a1)))
noncomputable def t76 (a0 : (M → Prop))  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (t9 (M := M) (fun x1_0 : M => (t16 (M := M) (t63 (M := M) x0_0 x1_0) (a0))))))
noncomputable def t81 (a0 : (M → Prop)) (a1 : (M → Prop))  : (M → Prop) := (t19 (M := M) (a0) (t75 (M := M) (a1) (t22 (M := M))))
noncomputable def t82 (a1 : M → M)  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (t9 (M := M) (fun x1_0 : M => (t10 (M := M) x0_0 (t63 (M := M) x1_0 (a1 x1_0)))))))
noncomputable def t83 (a0 : (M → Prop)) (a1 : M)  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (t16 (M := M) (t63 (M := M) (a1) x0_0) (a0))))
noncomputable def t84 (a0 : (M → Prop)) (a1 : M)  : M := (t40 (M := M) (t15 (M := M) (fun x1_0 : M => (t16 (M := M) (t63 (M := M) (a1) x1_0) (a0)))))
noncomputable def t89 (a1 : M → (M → Prop))  : (M → Prop) := (t73 (M := M) (fun x0_0 : M => (t15 (M := M) (fun x1_0 : M => (t16 (M := M) (t63 (M := M) (t65 (M := M) x0_0) x1_0) (t25 (M := M) (t64 (M := M) x0_0) (fun x3_1 : M => (a1 x3_1))))))))
noncomputable def t90 (a0 : (M → Prop))  : M := (t40 (M := M) (t15 (M := M) (fun x1_0 : M => (t2 (t16 (M := M) x1_0 (a0)) (t8 (M := M) (fun x3_0 : M => (t0 (t16 (M := M) x3_0 (a0)) (t47 (M := M) x1_0 x3_0))))))))
noncomputable def t105 (a0 : M) (a1 : M)  : M := (t40 (M := M) (t15 (M := M) (fun x1_0 : M => (t8 (M := M) (fun x2_0 : M => (t3 (t58 (M := M) x2_0 x1_0) (t2 (t58 (M := M) x2_0 (a0)) (t58 (M := M) x2_0 (a1)))))))))
noncomputable def t106 (a0 : M) (a1 : M)  : M := (t90 (M := M) (t15 (M := M) (fun x1_0 : M => (t2 (t48 (M := M) (t28 (M := M)) x1_0) (t9 (M := M) (fun x3_0 : M => (t9 (M := M) (fun x4_0 : M => (t10 (M := M) (t45 (M := M) x3_0 (a0)) (t44 (M := M) (t45 (M := M) x4_0 (a1)) x1_0))))))))))
noncomputable def t107 (a0 : M) (a1 : M)  : Prop := (t10 (M := M) (t105 (M := M) (a0) (a1)) (t30 (M := M)))
noncomputable def t109 (a0 : M)  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (t2 (t2 (t2 (t48 (M := M) (t28 (M := M)) (t64 (M := M) (a0))) (t48 (M := M) (t28 (M := M)) (t65 (M := M) (a0)))) (t8 (M := M) (fun x3_0 : M => (t0 (t2 (t48 (M := M) (t28 (M := M)) x3_0) (t47 (M := M) x3_0 x0_0)) (t58 (M := M) x3_0 (t64 (M := M) (a0))))))) (t58 (M := M) (t29 (M := M) (t45 (M := M) (t64 (M := M) (a0)) (t29 (M := M) x0_0))) (t65 (M := M) (a0))))))
noncomputable def t110 (a0 : M) (a1 : (M → Prop)) (a2 : M)  : M := (t40 (M := M) (t15 (M := M) (fun x1_0 : M => (t9 (M := M) (fun x2_0 : M => (t2 (t2 (t10 (M := M) (t84 (M := M) (t109 (M := M) x2_0) (t28 (M := M))) (a0)) (t10 (M := M) (t84 (M := M) (t109 (M := M) x2_0) (a2)) x1_0)) (t8 (M := M) (fun x4_0 : M => (t0 (t48 (M := M) x4_0 (a2)) (t10 (M := M) (t84 (M := M) (t109 (M := M) x2_0) (t29 (M := M) x4_0)) (t84 (M := M) (a1) (t84 (M := M) (t109 (M := M) x2_0) x4_0))))))))))))
noncomputable def t111 (a0 : M) (a1 : (M → Prop)) (a2 : M)  : M := (t110 (M := M) (t63 (M := M) (t28 (M := M)) (a0)) (t82 (M := M) (fun x1_0 : M => (t63 (M := M) (t29 (M := M) (t64 (M := M) x1_0)) (t84 (M := M) (a1) x1_0)))) (a2))
noncomputable def t112 (a0 : M) (a1 : (M → Prop)) (a2 : M)  : M := (t65 (M := M) (t111 (M := M) (a0) (a1) (a2)))
noncomputable def t117 (a0 : M) (a1 : M)  : M := (t110 (M := M) (t30 (M := M)) (t82 (M := M) (fun x1_0 : M => (t45 (M := M) (a0) x1_0))) (a1))
noncomputable def t118 (a0 : M) (a1 : M)  : M := (t45 (M := M) (a0) (t117 (M := M) (t31 (M := M)) (a1)))
noncomputable def t119 (a0 : M) (a1 : M)  : M := (t56 (M := M) (a0) (t117 (M := M) (t31 (M := M)) (a1)))
theorem b746 (a1 : (M → Prop)) (a2 : M)  : (t0 (t17 (M := M) (a1) (t15 (M := M) (fun x2_0 : M => (t10 (M := M) x2_0 (a2))))) (t10 (M := M) (t40 (M := M) (a1)) (a2))) := ZF209.MM0ModelPeano.«theid» a1 a2 
theorem b747 (a2 : (M → Prop))  : (t0 (t1 (t9 (M := M) (fun x2_0 : M => (t17 (M := M) (a2) (t15 (M := M) (fun x4_0 : M => (t10 (M := M) x4_0 x2_0))))))) (t10 (M := M) (t40 (M := M) (a2)) (t28 (M := M)))) := ZF209.MM0ModelPeano.«the0» a2 
theorem b790 (a0 : M) (a1 : M) (a2 : M) (a3 : M)  : (t0 (t10 (M := M) (a0) (a1)) (t0 (t10 (M := M) (a2) (a3)) (t10 (M := M) (t44 (M := M) (a0) (a2)) (t44 (M := M) (a1) (a3))))) := ZF209.MM0ModelPeano.«addeq» a0 a1 a2 a3 
theorem b791 (a0 : M) (a1 : M) (a2 : M) (a3 : M)  : (t0 (t10 (M := M) (a0) (a1)) (t0 (t10 (M := M) (a2) (a3)) (t10 (M := M) (t45 (M := M) (a0) (a2)) (t45 (M := M) (a1) (a3))))) := ZF209.MM0ModelPeano.«muleq» a0 a1 a2 a3 
theorem b792 (a0 : M)  : (t10 (M := M) (t44 (M := M) (a0) (t28 (M := M))) (a0)) := ZF209.MM0ModelPeano.«add0» a0 
theorem b793 (a0 : M) (a1 : M)  : (t10 (M := M) (t44 (M := M) (a0) (t29 (M := M) (a1))) (t29 (M := M) (t44 (M := M) (a0) (a1)))) := ZF209.MM0ModelPeano.«addS» a0 a1 
theorem b794 (a0 : M)  : (t10 (M := M) (t45 (M := M) (a0) (t28 (M := M))) (t28 (M := M))) := ZF209.MM0ModelPeano.«mul0» a0 
theorem b795 (a0 : M) (a1 : M)  : (t10 (M := M) (t45 (M := M) (a0) (t29 (M := M) (a1))) (t44 (M := M) (t45 (M := M) (a0) (a1)) (a0))) := ZF209.MM0ModelPeano.«mulS» a0 a1 
-- Actual MMB 743 sucne0
theorem p743 (a0 : M) (a1 : M)  : (t0 (t10 (M := M) (a0) (t29 (M := M) (a1))) (t13 (M := M) (a0) (t28 (M := M)))) := by
  let e0  : M := (t29 (M := M) (a1))
  let e1  : M := (t28 (M := M))
  have v0 := b734 (M := M) (a1)
  have v1 := p512 (M := M) (a0) (e0) (e1)
  have v2 := p122 ((show Prop from (t10 (M := M) (a0) (e0)))) ((show Prop from (t13 (M := M) (e0) (e1)))) ((show Prop from (t13 (M := M) (a0) (e1)))) (v0) (v1)
  exact v2
-- Actual MMB 744 exsuc
theorem p744 (a1 : M)  : (t3 (t13 (M := M) (a1) (t28 (M := M))) (t9 (M := M) (fun x1_0 : M => (t10 (M := M) (a1) (t29 (M := M) x1_0))))) := by
  let e0  : M := (t28 (M := M))
  let e1 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e2 (u0 : M) : Prop := (t10 (M := M) u0 (e0))
  let e3  : Prop := (t10 (M := M) (a1) (e0))
  let e4 (u0 : M) : Prop := (t13 (M := M) u0 (e0))
  let e5  : Prop := (t13 (M := M) (a1) (e0))
  let e6 (u0 : M) : Prop := (t3 (e4 u0) (e5))
  let e7 (u0 : M) : Prop := (t0 (e1 u0) (e6 u0))
  let e8 (u0 : M) : M := (t29 (M := M) u0)
  let e9 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (e8 u1))
  let e10 (u0 : M) : Prop := (t10 (M := M) (a1) (e8 u0))
  let e11 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (e9 u0 x0_0)))
  let e12  : Prop := (t9 (M := M) (fun x0_0 : M => (e10 x0_0)))
  let e13  : Prop := (t10 (M := M) (e0) (e0))
  let e14  : Prop := (t1 (e13))
  let e15 (u0 : M) : Prop := (t3 (e4 u0) (e14))
  let e16 (u0 : M) : Prop := (t0 (e2 u0) (e15 u0))
  let e17 (u0 : M) : Prop := (t10 (M := M) (e0) (e8 u0))
  let e18  : Prop := (t9 (M := M) (fun x0_0 : M => (e17 x0_0)))
  let e19 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e20 (u0 : M) : Prop := (t10 (M := M) u0 (e0))
  let e21 (u0 : M) : Prop := (t1 (e20 u0))
  let e22 (u0 : M) (u1 : M) : Prop := (t3 (e4 u0) (e21 u1))
  let e23 (u0 : M) (u1 : M) : Prop := (t0 (e19 u0 u1) (e22 u0 u1))
  let e24 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (e8 u1))
  let e25 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (e24 u0 x0_0)))
  let e26 (u0 : M) : M := (t29 (M := M) u0)
  let e27 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (e26 u1))
  let e28 (u0 : M) : Prop := (t10 (M := M) (e26 u0) (e0))
  let e29 (u0 : M) : Prop := (t1 (e28 u0))
  let e30 (u0 : M) (u1 : M) : Prop := (t3 (e4 u0) (e29 u1))
  let e31 (u0 : M) (u1 : M) : Prop := (t0 (e27 u0 u1) (e30 u0 u1))
  let e32 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e26 u0) (e8 u1))
  let e33 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (e32 u0 x0_0)))
  let e34  : Prop := (t0 (e14) (e18))
  let e35 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e36 (u0 : M) : Prop := (t10 (M := M) (e26 u0) (e26 u0))
  let e37 (u0 : M) : Prop := (t0 (e21 u0) (e25 u0))
  let e38 (u0 : M) : Prop := (t0 (e29 u0) (e33 u0))
  let e39 (u0 : M) : Prop := (t0 (e4 u0) (e11 u0))
  let e40  : Prop := (t0 (e5) (e12))
  have v0 := fun z0 : M => p346 (M := M) z0 (a1) (e0)
  have v1 := fun z0 : M => p187 (e1 z0) (e2 z0) (e3) (v0 z0)
  have v2 : (∀ z0 : M, (e7 z0)) := (show (∀ z0 : M, (e7 z0)) from v1)
  have v3 := fun z0 : M => fun z1 : M => p346 (M := M) z0 (a1) (e8 z1)
  have v4 := fun z0 : M => p379 (M := M) (e1 z0) (fun w1 : M => (e9 z0 w1)) (fun w1 : M => (e10 w1)) ((fun w1 : M => v3 z0 w1))
  have v5 := fun z0 : M => p188 (e1 z0) (e4 z0) (e5) (e11 z0) (e12) (v2 z0) (v4 z0)
  have v6 := fun z0 : M => p346 (M := M) z0 (e0) (e0)
  have v7 := fun z0 : M => p187 (e2 z0) (e2 z0) (e13) (v6 z0)
  have v8 : (∀ z0 : M, (e16 z0)) := (show (∀ z0 : M, (e16 z0)) from v7)
  have v9 := fun z0 : M => fun z1 : M => p346 (M := M) z0 (e0) (e8 z1)
  have v10 := fun z0 : M => p379 (M := M) (e2 z0) (fun w1 : M => (e9 z0 w1)) (fun w1 : M => (e17 w1)) ((fun w1 : M => v9 z0 w1))
  have v11 := fun z0 : M => p188 (e2 z0) (e4 z0) (e14) (e11 z0) (e18) (v8 z0) (v10 z0)
  have v12 := fun z0 : M => fun z1 : M => p346 (M := M) z0 z1 (e0)
  have v13 := fun z0 : M => fun z1 : M => p187 (e19 z0 z1) (e2 z0) (e20 z1) (v12 z0 z1)
  have v14 : (∀ z0 : M, (∀ z1 : M, (e23 z0 z1))) := (show (∀ z0 : M, (∀ z1 : M, (e23 z0 z1))) from v13)
  have v15 := fun z0 : M => fun z1 : M => fun z2 : M => p346 (M := M) z0 z1 (e8 z2)
  have v16 := fun z0 : M => fun z1 : M => p379 (M := M) (e19 z0 z1) (fun w1 : M => (e9 z0 w1)) (fun w1 : M => (e24 z1 w1)) ((fun w1 : M => v15 z0 z1 w1))
  have v17 := fun z0 : M => fun z1 : M => p188 (e19 z0 z1) (e4 z0) (e21 z1) (e11 z0) (e25 z1) (v14 z0 z1) (v16 z0 z1)
  have v18 := fun z0 : M => fun z1 : M => p346 (M := M) z0 (e26 z1) (e0)
  have v19 := fun z0 : M => fun z1 : M => p187 (e27 z0 z1) (e2 z0) (e28 z1) (v18 z0 z1)
  have v20 : (∀ z0 : M, (∀ z1 : M, (e31 z0 z1))) := (show (∀ z0 : M, (∀ z1 : M, (e31 z0 z1))) from v19)
  have v21 := fun z0 : M => fun z1 : M => fun z2 : M => p346 (M := M) z0 (e26 z1) (e8 z2)
  have v22 := fun z0 : M => fun z1 : M => p379 (M := M) (e27 z0 z1) (fun w1 : M => (e9 z0 w1)) (fun w1 : M => (e32 z1 w1)) ((fun w1 : M => v21 z0 z1 w1))
  have v23 := fun z0 : M => fun z1 : M => p188 (e27 z0 z1) (e4 z0) (e29 z1) (e11 z0) (e33 z1) (v20 z0 z1) (v22 z0 z1)
  have v24 := p27 (e13) (e18)
  have v25 := p340 (M := M) (e0)
  have v26 := b3 (e13) (e34) (v24) (v25)
  have v27 := fun z0 : M => fun z1 : M => p739 (M := M) z1 z0
  have v28 := fun z0 : M => fun z1 : M => p349 (M := M) (e35 z0 z1) (e26 z0) (e8 z1) (e26 z0) (v27 z0 z1)
  have v29 := fun z0 : M => p445 (M := M) z0 (fun w0 : M => (e32 z0 w0)) (e36 z0) ((fun w0 : M => v28 z0 w0))
  have v30 := fun z0 : M => p340 (M := M) (e26 z0)
  have v31 := fun z0 : M => b3 (e36 z0) (e33 z0) (v29 z0) (v30 z0)
  have v32 := fun z0 : M => p4 (e29 z0) (e33 z0) (v31 z0)
  have v33 := fun z0 : M => p4 (e37 z0) (e38 z0) (v32 z0)
  let certificate : ZF209.MM0ModelPeano.FormulaCertificate (fun _ : Nat => (0:M)) 1 (fun v => e39 (v 0)) := {
    formula := “x. x ≠ 0 → ∃ y, x = y+1”
    correct := by
      intro v
      classical
      simp [e39,e4,e11,e9,e8,e0,t0,t1,t8,t9,t10,t13,t28,t29]
  }
  have v34 := p741 (M := M) (fun _ : Nat => (0:M)) (fun w1 : M => (a1)) (fun w0 : M => (e39 w0)) (fun w1 : M => (e34)) (fun w1 : M => (e40)) (fun w1 : M => (e37 w1)) (fun w1 : M => (e38 w1)) certificate ((fun w0 : M => (fun w1 : M => v5 w0))) ((fun w0 : M => (fun w1 : M => v11 w0))) ((fun w0 : M => (fun w1 : M => v17 w0 w1))) ((fun w0 : M => (fun w1 : M => v23 w0 w1))) ((fun w1 : M => v26)) ((fun w1 : M => v33 w1)) 0
  have v35 := fun z0 : M => p743 (M := M) (a1) z0
  have v36 := p339 (M := M) (fun w0 : M => (e10 w0)) (e5) ((fun w0 : M => v35 w0))
  have v37 := p112 (e5) (e12) (v34) (v36)
  exact v37
-- Actual MMB 745 eqsucext
theorem p748 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (h0 : (t0 (a0) (t17 (M := M) (a1) (a2)))) : (t0 (a0) (t10 (M := M) (t40 (M := M) (a1)) (t40 (M := M) (a2)))) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e1 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e0 x0_0 u0)))
  let e2 (u0 : M) : Prop := (t17 (M := M) (a1) (e1 u0))
  let e3  : M := (t40 (M := M) (a1))
  let e4 (u0 : M) : Prop := (t10 (M := M) (e3) u0)
  let e6 (u0 : M) : Prop := (t17 (M := M) (a2) (e1 u0))
  let e7 (u0 : M) : Prop := (t0 (e2 u0) (e6 u0))
  let e8 (u0 : M) : Prop := (t2 (a0) (e2 u0))
  let e9  : M := (t40 (M := M) (a2))
  let e10 (u0 : M) : Prop := (t10 (M := M) (e9) u0)
  let e11  : Prop := (t10 (M := M) (e3) (e9))
  let e12  : Prop := (t9 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e13  : Prop := (t1 (e12))
  let e14  : M := (t28 (M := M))
  let e16  : Prop := (t9 (M := M) (fun x0_0 : M => (e6 x0_0)))
  let e17  : Prop := (t1 (e16))
  let e18  : Prop := (t2 (a0) (e13))
  have v0 := fun z0 : M => b746 (M := M) (a1) z0
  have v1 := fun z0 : M => p63 (a0) (e2 z0) (e4 z0) (v0 z0)
  have v2 := fun z0 : M => b746 (M := M) (a2) z0
  have v3 := fun z0 : M => p559 (M := M) (a2) (a1) (e1 z0)
  have v4 := fun z0 : M => p10 (a0) ((show Prop from (t17 (M := M) (a1) (a2)))) (e7 z0) (v3 z0) (h0)
  have v5 := fun z0 : M => p83 (a0) (e2 z0) (e6 z0) (v4 z0)
  have v6 := fun z0 : M => p10 (e8 z0) (e6 z0) (e10 z0) (v2 z0) (v5 z0)
  have v7 := fun z0 : M => p359 (M := M) (e8 z0) (e3) z0 (e9) (v1 z0) (v6 z0)
  have v8 := p425 (M := M) (a0) (fun w0 : M => (e2 w0)) (e11) ((fun w0 : M => v7 w0))
  have v9 := b747 (M := M) (a1)
  have v10 := p63 (a0) (e13) ((show Prop from (t10 (M := M) (e3) (e14)))) (v9)
  have v11 := b747 (M := M) (a2)
  have v12 := fun z0 : M => p579 (M := M) (a0) (a1) (a2) (e1 z0) (h0)
  have v13 := p379 (M := M) (a0) (fun w1 : M => (e2 w1)) (fun w1 : M => (e6 w1)) ((fun w1 : M => v12 w1))
  have v14 := p187 (a0) (e12) (e16) (v13)
  have v15 := p175 (a0) (e13) (e17) (v14)
  have v16 := p10 (e18) (e17) ((show Prop from (t10 (M := M) (e9) (e14)))) (v11) (v15)
  have v17 := p359 (M := M) (e18) (e3) (e14) (e9) (v10) (v16)
  have v18 := p84 (a0) (e13) (e11) (v17)
  have v19 := p43 (a0) (e12) (e11) (v8) (v18)
  exact v19
-- Actual MMB 749 theeq
theorem p749 (a0 : (M → Prop)) (a1 : (M → Prop))  : (t0 (t17 (M := M) (a0) (a1)) (t10 (M := M) (t40 (M := M) (a0)) (t40 (M := M) (a1)))) := by
  let e0  : Prop := (t17 (M := M) (a0) (a1))
  have v0 := p8 (e0)
  have v1 := p748 (M := M) (e0) (a0) (a1) (v0)
  exact v1
-- Actual MMB 750 eqthed
theorem p750 (a0 : (M → Prop)) (a1 : Prop) (a2 : M) (h0 : (∀ z0 : M, (t0 (a1) (t3 (t16 (M := M) z0 (a0)) (t10 (M := M) z0 (a2)))))) : (t0 (a1) (t10 (M := M) (t40 (M := M) (a0)) (a2))) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e1 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e2 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e3  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4 (u0 : M) : Prop := (t16 (M := M) u0 (e3))
  have v0 := b746 (M := M) (a0) (a2)
  have v1 := fun z0 : M => fun z1 : M => p346 (M := M) z0 z1 (a2)
  have v2 := fun z0 : M => p593 (M := M) z0 (fun w0 : M => (e0 w0)) (e1 z0) ((fun w0 : M => v1 w0 z0))
  have v3 := fun z0 : M => p160 (a1) (e2 z0) (e1 z0) (e4 z0) (v2 z0) (h0 z0)
  have v4 := p587 (M := M) (a0) (e3) (a1) ((fun w3 : M => v3 w3))
  have v5 := p10 (a1) ((show Prop from (t17 (M := M) (a0) (e3)))) ((show Prop from (t10 (M := M) ((show M from (t40 (M := M) (a0)))) (a2)))) (v0) (v4)
  exact v5
-- Actual MMB 751 eqtheabd
theorem p751 (a0 : Prop) (a1 : M) (a3 : M → Prop) (h0 : (∀ z0 : M, (t0 (a0) (t3 (a3 z0) (t10 (M := M) z0 (a1)))))) : (t0 (a0) (t10 (M := M) (t40 (M := M) (t15 (M := M) (fun x3_0 : M => (a3 x3_0)))) (a1))) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t3 (a3 u0) (e0 u0))
  let e2 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e3 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a3 x0_1)))
  let e4 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e5 (u0 : M) : Prop := (t3 (e3 u0) (e2 u0))
  let e7  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a3 x0_0)))
  let e8 (u0 : M) : Prop := (t16 (M := M) u0 (e7))
  have v0 := fun z0 : M => b552 (M := M) z0 (fun w1 : M => (a3 w1))
  have v1 := p338 (M := M) (a0) (fun w0 : M => (e1 w0)) ((fun w0 : M => h0 w0))
  have v2 := fun z0 : M => p518 (M := M) z0 (fun w0 : M => (a3 w0))
  have v3 := fun z0 : M => p405 (M := M) (e2 z0)
  have v4 := fun z0 : M => p415 (M := M) (fun w0 : M => (e3 z0)) (fun w0 : M => (e2 z0)) (v2 z0) (v3 z0)
  have v5 := fun z0 : M => fun z1 : M => p516 (M := M) z0 (fun w0 : M => (a3 w0)) z1
  have v6 := fun z0 : M => fun z1 : M => p346 (M := M) z1 z0 (a1)
  have v7 := fun z0 : M => fun z1 : M => p233 (e4 z0 z1) (a3 z1) (e3 z0) (e0 z1) (e2 z0) (v5 z0 z1) (v6 z0 z1)
  have v8 := fun z0 : M => p429 (M := M) z0 (fun w0 : M => (e1 w0)) (fun w0 : M => (e5 z0)) (v4 z0) ((fun w0 : M => v7 z0 w0)) 0
  have v9 := fun z0 : M => p11 (a0) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e1 x0_0))))) (e5 z0) (v1) (v8 z0)
  have v10 := fun z0 : M => p157 (a0) (e8 z0) (e3 z0) (e2 z0) (v0 z0) (v9 z0)
  have v11 := p750 (M := M) (e7) (a0) (a1) ((fun w3 : M => v10 w3))
  exact v11
-- Actual MMB 752 eqthe0d
theorem p752 (a0 : (M → Prop)) (a1 : Prop) (h0 : (∀ z0 : M, (t0 (a1) (t0 (t16 (M := M) z0 (a0)) (t10 (M := M) z0 (t28 (M := M))))))) : (t0 (a1) (t10 (M := M) (t40 (M := M) (a0)) (t28 (M := M)))) := by
  let e0  : M := (t28 (M := M))
  let e1 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e2 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e1 x0_0 u0)))
  let e3 (u0 : M) : Prop := (t17 (M := M) (a0) (e2 u0))
  let e4 (u0 : M) : Prop := (t10 (M := M) u0 (e0))
  let e5 (u0 : M) : Prop := (t10 (M := M) u0 (e0))
  let e6 (u0 : M) : Prop := (t10 (M := M) u0 u0)
  let e7 (u0 : M) : Prop := (t16 (M := M) u0 (e2 u0))
  let e8 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e9 (u0 : M) : Prop := (t3 (e8 u0) (e7 u0))
  let e10 (u0 : M) : Prop := (t2 (a1) (e3 u0))
  let e11 (u0 : M) : Prop := (t0 (e8 u0) (e4 u0))
  let e12  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e5 x0_0)))
  let e13 (u0 : M) : Prop := (t17 (M := M) (e2 u0) (e12))
  let e16  : Prop := (t10 (M := M) ((show M from (t40 (M := M) (a0)))) (e0))
  let e17  : Prop := (t9 (M := M) (fun x0_0 : M => (e3 x0_0)))
  have v0 := b746 (M := M) (a0) (e0)
  have v1 := fun z0 : M => p54 (a1) (e3 z0)
  have v2 := fun z0 : M => fun z1 : M => p347 (M := M) z0 z1 (e0)
  have v3 := fun z0 : M => p584 (M := M) (e4 z0) (fun w1 : M => (e1 w1 z0)) (fun w1 : M => (e5 w1)) ((fun w1 : M => v2 w1 z0))
  have v4 := fun z0 : M => fun z1 : M => p346 (M := M) z0 z1 z1
  have v5 := fun z0 : M => p593 (M := M) z0 (fun w0 : M => (e1 w0 z0)) (e6 z0) ((fun w0 : M => v4 w0 z0))
  have v6 := fun z0 : M => p340 (M := M) z0
  have v7 := fun z0 : M => p118 (e6 z0) (e7 z0) (v5 z0) (v6 z0)
  have v8 := fun z0 : M => p573 (M := M) (a0) (e2 z0) z0
  have v9 := fun z0 : M => p63 (a1) (e3 z0) (e9 z0) (v8 z0)
  have v10 := fun z0 : M => p122 (e10 z0) (e7 z0) (e8 z0) (v7 z0) (v9 z0)
  have v11 := fun z0 : M => p62 (a1) (e3 z0) (e11 z0) (h0 z0)
  have v12 := fun z0 : M => p6 (e10 z0) (e8 z0) (e4 z0) (v10 z0) (v11 z0)
  have v13 := fun z0 : M => p10 (e10 z0) (e4 z0) (e13 z0) (v3 z0) (v12 z0)
  have v14 := fun z0 : M => p564 (M := M) (a0) (e2 z0) (e12) (e10 z0) (v1 z0) (v13 z0)
  have v15 := fun z0 : M => p10 (e10 z0) ((show Prop from (t17 (M := M) (a0) (e12)))) (e16) (v0) (v14 z0)
  have v16 := p425 (M := M) (a1) (fun w0 : M => (e3 w0)) (e16) ((fun w0 : M => v15 w0))
  have v17 := b747 (M := M) (a0)
  have v18 := p4 (a1) ((show Prop from (t0 ((show Prop from (t1 (e17)))) (e16)))) (v17)
  have v19 := p43 (a1) (e17) (e16) (v16) (v18)
  exact v19
-- Actual MMB 753 eqthe0abd
theorem p753 (a0 : Prop) (a2 : M → Prop) (h0 : (∀ z0 : M, (t0 (a0) (t0 (a2 z0) (t10 (M := M) z0 (t28 (M := M))))))) : (t0 (a0) (t10 (M := M) (t40 (M := M) (t15 (M := M) (fun x3_0 : M => (a2 x3_0)))) (t28 (M := M)))) := by
  let e0  : M := (t28 (M := M))
  let e1 (u0 : M) : Prop := (t10 (M := M) u0 (e0))
  let e2 (u0 : M) : Prop := (t0 (a2 u0) (e1 u0))
  let e3 (u0 : M) : Prop := (t10 (M := M) u0 (e0))
  let e4 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a2 x0_1)))
  let e5 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e6 (u0 : M) : Prop := (t0 (e4 u0) (e3 u0))
  let e8  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a2 x0_0)))
  let e9 (u0 : M) : Prop := (t16 (M := M) u0 (e8))
  have v0 := fun z0 : M => b552 (M := M) z0 (fun w1 : M => (a2 w1))
  have v1 := p338 (M := M) (a0) (fun w0 : M => (e2 w0)) ((fun w0 : M => h0 w0))
  have v2 := fun z0 : M => p518 (M := M) z0 (fun w0 : M => (a2 w0))
  have v3 := fun z0 : M => p405 (M := M) (e3 z0)
  have v4 := fun z0 : M => p412 (M := M) (fun w0 : M => (e4 z0)) (fun w0 : M => (e3 z0)) (v2 z0) (v3 z0)
  have v5 := fun z0 : M => fun z1 : M => p516 (M := M) z0 (fun w0 : M => (a2 w0)) z1
  have v6 := fun z0 : M => fun z1 : M => p346 (M := M) z1 z0 (e0)
  have v7 := fun z0 : M => fun z1 : M => p188 (e5 z0 z1) (a2 z1) (e4 z0) (e1 z1) (e3 z0) (v5 z0 z1) (v6 z0 z1)
  have v8 := fun z0 : M => p429 (M := M) z0 (fun w0 : M => (e2 w0)) (fun w0 : M => (e6 z0)) (v4 z0) ((fun w0 : M => v7 z0 w0)) 0
  have v9 := fun z0 : M => p11 (a0) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e2 x0_0))))) (e6 z0) (v1) (v8 z0)
  have v10 := fun z0 : M => p161 (a0) (e9 z0) (e4 z0) (e3 z0) (v0 z0) (v9 z0)
  have v11 := p752 (M := M) (e8) (a0) ((fun w2 : M => v10 w2))
  exact v11
-- Actual MMB 754 eqtheb
theorem p754 (a0 : (M → Prop)) (a1 : M)  : (t3 (t10 (M := M) (a1) (t40 (M := M) (a0))) (t4 (t17 (M := M) (a0) (t15 (M := M) (fun x3_0 : M => (t10 (M := M) x3_0 (a1))))) (t2 (t1 (t9 (M := M) (fun x4_0 : M => (t17 (M := M) (a0) (t15 (M := M) (fun x6_0 : M => (t10 (M := M) x6_0 x4_0))))))) (t10 (M := M) (a1) (t28 (M := M)))))) := by
  let e0  : M := (t40 (M := M) (a0))
  let e1  : Prop := (t10 (M := M) (a1) (e0))
  let e2 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e3  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e4  : Prop := (t17 (M := M) (a0) (e3))
  let e5 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e6 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e5 x0_0 u0)))
  let e7 (u0 : M) : Prop := (t17 (M := M) (a0) (e6 u0))
  let e8  : Prop := (t9 (M := M) (fun x0_0 : M => (e7 x0_0)))
  let e9  : M := (t28 (M := M))
  let e10  : Prop := (t10 (M := M) (a1) (e9))
  let e11  : Prop := (t1 (e8))
  let e12  : Prop := (t2 (e11) (e10))
  let e13 (u0 : M) : Prop := (t10 (M := M) (a1) u0)
  let e14 (u0 : M) : Prop := (t10 (M := M) (e0) u0)
  let e15 (u0 : M) : Prop := (t2 (e1) (e7 u0))
  let e16 (u0 : M) : Prop := (t3 (e4) (e7 u0))
  let e17  : Prop := (t4 (e4) (e12))
  let e19  : Prop := (t2 (e1) (e11))
  have v0 := p405 (M := M) (e1)
  have v1 := p405 (M := M) (e4)
  have v2 := p416 (M := M) (fun w0 : M => (e7 w0))
  have v3 := p411 (M := M) (fun w0 : M => (e8)) (v2)
  have v4 := p405 (M := M) (e10)
  have v5 := p413 (M := M) (fun w0 : M => (e11)) (fun w0 : M => (e10)) (v3) (v4)
  have v6 := p414 (M := M) (fun w0 : M => (e4)) (fun w0 : M => (e12)) (v1) (v5)
  have v7 := fun z0 : M => fun z1 : M => p347 (M := M) z0 (a1) z1
  have v8 := fun z0 : M => p584 (M := M) (e13 z0) (fun w1 : M => (e2 w1)) (fun w1 : M => (e5 w1 z0)) ((fun w1 : M => v7 w1 z0))
  have v9 := fun z0 : M => p581 (M := M) (e13 z0) (a0) (e3) (e6 z0) (v8 z0)
  have v10 := fun z0 : M => p53 (e1) (e7 z0)
  have v11 := fun z0 : M => b746 (M := M) (a0) z0
  have v12 := fun z0 : M => p63 (e1) (e7 z0) (e14 z0) (v11 z0)
  have v13 := fun z0 : M => p357 (M := M) (e15 z0) (a1) (e0) z0 (v10 z0) (v12 z0)
  have v14 := fun z0 : M => p10 (e15 z0) (e13 z0) (e16 z0) (v9 z0) (v13 z0)
  have v15 := fun z0 : M => p54 (e1) (e7 z0)
  have v16 := fun z0 : M => p120 (e15 z0) (e7 z0) (e4) (v14 z0) (v15 z0)
  have v17 := fun z0 : M => p254 (e15 z0) (e4) (e12) (v16 z0)
  have v18 := fun z0 : M => p84 (e1) (e7 z0) (e17) (v17 z0)
  have v19 := p421 (M := M) (fun w0 : M => (e1)) (fun w0 : M => (e7 w0)) (fun w0 : M => (e17)) (v0) (v6) ((fun w0 : M => v18 w0)) 0
  have v20 := p83 (e1) (e8) (e17) (v19)
  have v21 := p54 (e1) (e11)
  have v22 := p53 (e1) (e11)
  have v23 := b747 (M := M) (a0)
  have v24 := p63 (e1) (e11) ((show Prop from (t10 (M := M) (e0) (e9)))) (v23)
  have v25 := p357 (M := M) (e19) (a1) (e0) (e9) (v22) (v24)
  have v26 := p58 (e19) (e11) (e10) (v21) (v25)
  have v27 := p255 (e19) (e4) (e12) (v26)
  have v28 := p99 (e1) (e8) (e17) (v20) (v27)
  have v29 := p256 (e4) (e12) (e1)
  have v30 := b746 (M := M) (a0) (a1)
  have v31 := p356 (M := M) (e4) (e0) (a1) (v30)
  have v32 := ((v29) (v31))
  have v33 := p54 (e11) (e10)
  have v34 := p356 (M := M) (e11) (e0) (e9) (v23)
  have v35 := p62 (e11) (e10) ((show Prop from (t10 (M := M) (e9) (e0)))) (v34)
  have v36 := p357 (M := M) (e12) (a1) (e9) (e0) (v33) (v35)
  have v37 := ((v32) (v36))
  have v38 := p112 (e1) (e17) (v28) (v37)
  exact v38
-- Actual MMB 755 nfthe
theorem p755 (a1 : M → (M → Prop)) (h0 : (t23 (M := M) (fun x0_0 : M => (a1 x0_0)))) : (t24 (M := M) (fun x0_0 : M => (t40 (M := M) (a1 x0_0)))) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e1 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e0 u0 x0_0)))
  let e2 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e3 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e2 x0_0 u0)))
  let e4 (u0 : M) (u1 : M) : Prop := (t17 (M := M) (a1 u1) (e3 u0))
  let e5 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (e4 x0_0 u0)))
  let e7 (u0 : M) : Prop := (t10 (M := M) u0 ((show M from (t28 (M := M)))))
  let e8 (u0 : M) : Prop := (t1 (e5 u0))
  let e9 (u0 : M) (u1 : M) : Prop := (t17 (M := M) (a1 u1) (e1 u0))
  let e10 (u0 : M) (u1 : M) : Prop := (t2 (e8 u1) (e7 u0))
  let e11 (u0 : M) : M := (t40 (M := M) (a1 u0))
  let e12 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (e11 u1))
  let e13 (u0 : M) (u1 : M) : Prop := (t4 (e9 u0 u1) (e10 u0 u1))
  have v0 := fun z0 : M => fun z1 : M => p754 (M := M) (a1 z1) z0
  have v1 := fun z0 : M => p673 (M := M) (e1 z0)
  have v2 := fun z0 : M => p686 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (e1 z0)) (h0) (v1 z0)
  have v3 := fun z0 : M => p673 (M := M) (e3 z0)
  have v4 := fun z0 : M => p686 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (e3 z0)) (h0) (v3 z0)
  have v5 := p417 (M := M) (fun w0 : M => (fun w1 : M => (e4 w1 w0))) ((fun w1 : M => v4 w1))
  have v6 := p411 (M := M) (fun w0 : M => (e5 w0)) (v5)
  have v7 := fun z0 : M => p405 (M := M) (e7 z0)
  have v8 := fun z0 : M => p413 (M := M) (fun w0 : M => (e8 w0)) (fun w0 : M => (e7 z0)) (v6) (v7 z0)
  have v9 := fun z0 : M => p414 (M := M) (fun w0 : M => (e9 z0 w0)) (fun w0 : M => (e10 z0 w0)) (v2 z0) (v8 z0)
  have v10 := fun z0 : M => p409 (M := M) (fun w0 : M => (e12 z0 w0)) (fun w0 : M => (e13 z0 w0)) ((fun w0 : M => v0 z0 w0)) (v9 z0)
  have v11 := p676 (M := M) (fun w0 : M => (e11 w0)) ((fun w1 : M => v10 w1))
  exact v11
-- Actual MMB 756 theoeqd
theorem p772 (a0 : Prop) (a2 : M → M) (a3 : M → M) (a4 : M → M) (a5 : M → M) (h0 : (∀ z0 : M, (t0 (a0) (t10 (M := M) (a2 z0) (a3 z0))))) (h1 : (∀ z0 : M, (t0 (a0) (t10 (M := M) (a4 z0) (a5 z0))))) : (∀ z0 : M, (t0 (a0) (t10 (M := M) (t43 (M := M) (a2 z0) (fun x2_1 : M => (a4 x2_1))) (t43 (M := M) (a3 z0) (fun x2_1 : M => (a5 x2_1)))))) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a4 u1))
  let e1 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a5 u1))
  let e2 (u0 : M) (u1 : M) : Prop := (t14 (M := M) (a2 u1) (fun x0_1 : M => (e0 u0 x0_1)))
  let e3 (u0 : M) (u1 : M) : Prop := (t14 (M := M) (a3 u1) (fun x0_1 : M => (e1 u0 x0_1)))
  let e4 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e2 x0_0 u0)))
  let e5 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e3 x0_0 u0)))
  let e6 (u0 : M) : M := (t43 (M := M) (a2 u0) (fun x0_1 : M => (a4 x0_1)))
  let e7 (u0 : M) : M := (t43 (M := M) (a3 u0) (fun x0_1 : M => (a5 x0_1)))
  let e8 (u0 : M) : Prop := (t10 (M := M) (e6 u0) (e7 u0))
  let e9 (u0 : M) : Prop := (t0 (a0) (e8 u0))
  have v0 := fun z0 : M => fun z1 : M => p349 (M := M) (a0) z0 (a4 z1) (a5 z1) (h1 z1)
  have v1 := fun z0 : M => fun z1 : M => p522 (M := M) (a0) (fun w1 : M => (a2 w1)) (fun w1 : M => (a3 w1)) (fun w1 : M => (e0 z0 w1)) (fun w1 : M => (e1 z0 w1)) ((fun w1 : M => h0 w1)) ((fun w1 : M => v0 z0 w1)) z1
  have v2 := fun z0 : M => p584 (M := M) (a0) (fun w1 : M => (e2 w1 z0)) (fun w1 : M => (e3 w1 z0)) ((fun w1 : M => v1 w1 z0))
  have v3 := fun z0 : M => p748 (M := M) (a0) (e4 z0) (e5 z0) (v2 z0)
  have v4 : (∀ z0 : M, (e9 z0)) := (show (∀ z0 : M, (e9 z0)) from v3)
  exact v4
-- Actual MMB 773 sbnq
theorem p773 (a1 : M) (a2 : M → M)  : (∀ z0 : M, (t0 (t10 (M := M) z0 (a1)) (t10 (M := M) (a2 z0) (t43 (M := M) (a1) (fun x2_1 : M => (a2 x2_1)))))) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a2 u1))
  let e1 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e2 (u0 : M) : Prop := (t14 (M := M) (a1) (fun x0_1 : M => (e0 u0 x0_1)))
  let e3  : M := (t43 (M := M) (a1) (fun x0_1 : M => (a2 x0_1)))
  let e4 (u0 : M) : Prop := (t10 (M := M) (e3) (a2 u0))
  let e5 (u0 : M) : Prop := (t0 (e1 u0) (e4 u0))
  have v0 := fun z0 : M => fun z1 : M => p516 (M := M) (a1) (fun w0 : M => (e0 z0 w0)) z1
  have v1 := fun z0 : M => fun z1 : M => p144 (e1 z1) (e0 z0 z1) (e2 z0) (v0 z0 z1)
  have v2 := fun z0 : M => p751 (M := M) (e1 z0) (a2 z0) (fun w2 : M => (e2 w2)) ((fun w2 : M => v1 w2 z0))
  have v3 : (∀ z0 : M, (e5 z0)) := (show (∀ z0 : M, (e5 z0)) from v2)
  have v4 := fun z0 : M => p356 (M := M) (e1 z0) (e3) (a2 z0) (v3 z0)
  exact v4
-- Actual MMB 774 nfsbn1h
theorem p774 (a1 : M → M) (a2 : M → M) (h0 : (t24 (M := M) (fun x0_0 : M => (a1 x0_0)))) : (t24 (M := M) (fun x0_0 : M => (t43 (M := M) (a1 x0_0) (fun x1_1 : M => (a2 x1_1))))) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a2 u1))
  let e1 (u0 : M) (u1 : M) : Prop := (t14 (M := M) (a1 u1) (fun x0_1 : M => (e0 u0 x0_1)))
  let e2 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e1 x0_0 u0)))
  let e3 (u0 : M) : M := (t43 (M := M) (a1 u0) (fun x0_1 : M => (a2 x0_1)))
  let e4  : Prop := (t24 (M := M) (fun x0_0 : M => (e3 x0_0)))
  have v0 := fun z0 : M => p681 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (e0 z0 w0)) (h0)
  have v1 := p685 (M := M) (fun w0 : M => (fun w1 : M => (e1 w1 w0))) ((fun w1 : M => v0 w1))
  have v2 := p755 (M := M) (fun w0 : M => (e2 w0)) (v1)
  have v3 : (e4) := (show (e4) from v2)
  exact v3
-- Actual MMB 775 nfsbn1
theorem p775 (a1 : M) (a2 : M → M)  : (t24 (M := M) (fun x0_0 : M => (t43 (M := M) (a1) (fun x1_1 : M => (a2 x1_1))))) := by
  have v0 := p674 (M := M) (a1)
  have v1 := p774 (M := M) (fun w0 : M => (a1)) (fun w0 : M => (a2 w0)) (v0)
  exact v1
-- Actual MMB 776 nfsbnh
theorem p776 (a2 : M → M → M) (a3 : M → M → M) (h0 : (∀ z0 : M, (t24 (M := M) (fun x0_0 : M => (a2 x0_0 z0))))) (h1 : (∀ z0 : M, (t24 (M := M) (fun x0_0 : M => (a3 x0_0 z0))))) : (∀ z0 : M, (t24 (M := M) (fun x0_0 : M => (t43 (M := M) (a2 x0_0 z0) (fun x1_1 : M => (a3 x0_0 x1_1)))))) := by
  let e0 (u0 : M) (u1 : M) (u2 : M) : Prop := (t10 (M := M) u0 (a3 u1 u2))
  let e1 (u0 : M) (u1 : M) (u2 : M) : Prop := (t14 (M := M) (a2 u1 u2) (fun x0_1 : M => (e0 u0 u1 x0_1)))
  let e2 (u0 : M) (u1 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e1 x0_0 u0 u1)))
  let e3 (u0 : M) (u1 : M) : M := (t43 (M := M) (a2 u0 u1) (fun x0_1 : M => (a3 u0 x0_1)))
  let e4 (u0 : M) : Prop := (t24 (M := M) (fun x0_0 : M => (e3 x0_0 u0)))
  have v0 := fun z0 : M => fun z1 : M => p680 (M := M) z0 (fun w1 : M => (a3 w1 z1)) (h1 z1)
  have v1 := fun z0 : M => fun z1 : M => p682 (M := M) (fun w0 : M => (fun w1 : M => (a2 w0 w1))) (fun w0 : M => (fun w1 : M => (e0 z0 w0 w1))) ((fun w1 : M => h0 w1)) ((fun w1 : M => v0 z0 w1)) z1
  have v2 := fun z0 : M => p685 (M := M) (fun w0 : M => (fun w1 : M => (e1 w1 w0 z0))) ((fun w1 : M => v1 w1 z0))
  have v3 := fun z0 : M => p755 (M := M) (fun w0 : M => (e2 w0 z0)) (v2 z0)
  have v4 : (∀ z0 : M, (e4 z0)) := (show (∀ z0 : M, (e4 z0)) from v3)
  exact v4
-- Actual MMB 777 nfsbn
theorem p779 (a1 : M) (a2 : M → M) (a3 : M → M) (h0 : (t24 (M := M) (fun x0_0 : M => (a3 x0_0)))) : (∀ z0 : M, (t0 (t8 (M := M) (fun x1_0 : M => (t0 (t10 (M := M) x1_0 (a1)) (t10 (M := M) (a2 x1_0) (a3 x1_0))))) (t10 (M := M) (t43 (M := M) (a1) (fun x2_1 : M => (a2 x2_1))) (a3 z0)))) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a2 u1))
  let e1 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a3 u1))
  let e2 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e3 (u0 : M) : Prop := (t10 (M := M) (a2 u0) (a3 u0))
  let e4 (u0 : M) (u1 : M) : Prop := (t3 (e0 u0 u1) (e1 u0 u1))
  let e5 (u0 : M) (u1 : M) : Prop := (t0 (e3 u1) (e4 u0 u1))
  let e6 (u0 : M) : Prop := (t0 (e2 u0) (e3 u0))
  let e7 (u0 : M) (u1 : M) : Prop := (t0 (e2 u1) (e4 u0 u1))
  let e8 (u0 : M) (u1 : M) : Prop := (t0 (e6 u1) (e7 u0 u1))
  let e9  : Prop := (t8 (M := M) (fun x0_0 : M => (e6 x0_0)))
  let e10 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e7 u0 x0_0)))
  let e11 (u0 : M) : Prop := (t14 (M := M) (a1) (fun x0_1 : M => (e0 u0 x0_1)))
  let e12 (u0 : M) (u1 : M) : Prop := (t3 (e11 u0) (e1 u0 u1))
  let e14 (u0 : M) : Prop := (t10 (M := M) ((show M from (t43 (M := M) (a1) (fun x0_1 : M => (a2 x0_1))))) (a3 u0))
  let e15 (u0 : M) : Prop := (t0 (e9) (e14 u0))
  have v0 := fun z0 : M => p680 (M := M) z0 (fun w1 : M => (a3 w1)) (h0)
  have v1 := fun z0 : M => fun z1 : M => p525 (M := M) (a1) (fun w0 : M => (e0 z0 w0)) (fun w0 : M => (e1 z0 w0)) (v0 z0) z1
  have v2 := fun z0 : M => fun z1 : M => p19 (e2 z1) (e3 z1) (e4 z0 z1)
  have v3 := fun z0 : M => fun z1 : M => p347 (M := M) z0 (a2 z1) (a3 z1)
  have v4 := fun z0 : M => fun z1 : M => b3 (e5 z0 z1) (e8 z0 z1) (v2 z0 z1) (v3 z0 z1)
  have v5 := fun z0 : M => p337 (M := M) (fun w0 : M => (e6 w0)) (fun w0 : M => (e7 z0 w0)) ((fun w0 : M => v4 z0 w0))
  have v6 := fun z0 : M => fun z1 : M => p10 (e9) (e10 z0) (e12 z0 z1) (v1 z0 z1) (v5 z0)
  have v7 := fun z0 : M => p751 (M := M) (e9) (a3 z0) (fun w2 : M => (e11 w2)) ((fun w2 : M => v6 w2 z0))
  have v8 : (∀ z0 : M, (e15 z0)) := (show (∀ z0 : M, (e15 z0)) from v7)
  exact v8
-- Actual MMB 780 sbneh
theorem p780 (a1 : M) (a2 : M → M) (a3 : M → M) (h0 : (t24 (M := M) (fun x0_0 : M => (a3 x0_0)))) (h1 : (∀ z0 : M, (t0 (t10 (M := M) z0 (a1)) (t10 (M := M) (a2 z0) (a3 z0))))) : (∀ z0 : M, (t10 (M := M) (t43 (M := M) (a1) (fun x1_1 : M => (a2 x1_1))) (a3 z0))) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t10 (M := M) (a2 u0) (a3 u0))
  let e2 (u0 : M) : Prop := (t0 (e0 u0) (e1 u0))
  let e5 (u0 : M) : Prop := (t10 (M := M) ((show M from (t43 (M := M) (a1) (fun x0_1 : M => (a2 x0_1))))) (a3 u0))
  have v0 := fun z0 : M => p779 (M := M) (a1) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3 w0)) (h0) z0
  have v1 := b325 (M := M) (fun w0 : M => (e2 w0)) ((fun w0 : M => h1 w0))
  have v2 := fun z0 : M => b3 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e2 x0_0))))) (e5 z0) (v0 z0) (v1)
  exact v2
-- Actual MMB 781 sbnet
theorem p781 (a1 : M) (a2 : M → M) (a3 : M)  : (t0 (t8 (M := M) (fun x1_0 : M => (t0 (t10 (M := M) x1_0 (a1)) (t10 (M := M) (a2 x1_0) (a3))))) (t10 (M := M) (t43 (M := M) (a1) (fun x2_1 : M => (a2 x2_1))) (a3))) := by
  have v0 := p674 (M := M) (a3)
  have v1 := p779 (M := M) (a1) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3)) (v0) 0
  exact v1
-- Actual MMB 782 sbne
theorem p782 (a1 : M) (a2 : M → M) (a3 : M) (h0 : (∀ z0 : M, (t0 (t10 (M := M) z0 (a1)) (t10 (M := M) (a2 z0) (a3))))) : (t10 (M := M) (t43 (M := M) (a1) (fun x1_1 : M => (a2 x1_1))) (a3)) := by
  have v0 := p674 (M := M) (a3)
  have v1 := p780 (M := M) (a1) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3)) (v0) ((fun w0 : M => h0 w0)) 0
  exact v1
-- Actual MMB 783 sbned
theorem p783 (a0 : Prop) (a2 : M) (a3 : M → M) (a4 : M) (h0 : (∀ z0 : M, (t0 (t2 (a0) (t10 (M := M) z0 (a2))) (t10 (M := M) (a3 z0) (a4))))) : (t0 (a0) (t10 (M := M) (t43 (M := M) (a2) (fun x2_1 : M => (a3 x2_1))) (a4))) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e1 (u0 : M) : Prop := (t10 (M := M) (a3 u0) (a4))
  let e2 (u0 : M) : Prop := (t0 (e0 u0) (e1 u0))
  have v0 := p781 (M := M) (a2) (fun w0 : M => (a3 w0)) (a4)
  have v1 := p372 (M := M) (a0) (fun w0 : M => (e0 w0)) (fun w0 : M => (e1 w0)) ((fun w0 : M => h0 w0))
  have v2 := p10 (a0) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e2 x0_0))))) ((show Prop from (t10 (M := M) ((show M from (t43 (M := M) (a2) (fun x0_1 : M => (a3 x0_1))))) (a4)))) (v0) (v1)
  exact v2
-- Actual MMB 784 sbneq1
theorem p784 (a1 : M → M) (a2 : M → M) (a3 : M → M)  : (∀ z0 : M, (t0 (t10 (M := M) (a1 z0) (a2 z0)) (t10 (M := M) (t43 (M := M) (a1 z0) (fun x2_1 : M => (a3 x2_1))) (t43 (M := M) (a2 z0) (fun x2_1 : M => (a3 x2_1)))))) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a3 u1))
  let e1 (u0 : M) : Prop := (t10 (M := M) (a1 u0) (a2 u0))
  let e2 (u0 : M) (u1 : M) : Prop := (t14 (M := M) (a1 u1) (fun x0_1 : M => (e0 u0 x0_1)))
  let e3 (u0 : M) (u1 : M) : Prop := (t14 (M := M) (a2 u1) (fun x0_1 : M => (e0 u0 x0_1)))
  let e4 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e2 x0_0 u0)))
  let e5 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e3 x0_0 u0)))
  let e6 (u0 : M) : M := (t43 (M := M) (a1 u0) (fun x0_1 : M => (a3 x0_1)))
  let e7 (u0 : M) : M := (t43 (M := M) (a2 u0) (fun x0_1 : M => (a3 x0_1)))
  let e8 (u0 : M) : Prop := (t10 (M := M) (e6 u0) (e7 u0))
  let e9 (u0 : M) : Prop := (t0 (e1 u0) (e8 u0))
  have v0 := fun z0 : M => fun z1 : M => p520 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (a2 w0)) (fun w0 : M => (e0 z0 w0)) z1
  have v1 := fun z0 : M => p584 (M := M) (e1 z0) (fun w1 : M => (e2 w1 z0)) (fun w1 : M => (e3 w1 z0)) ((fun w1 : M => v0 w1 z0))
  have v2 := fun z0 : M => p748 (M := M) (e1 z0) (e4 z0) (e5 z0) (v1 z0)
  have v3 : (∀ z0 : M, (e9 z0)) := (show (∀ z0 : M, (e9 z0)) from v2)
  exact v3
-- Actual MMB 785 sbneq1d
theorem p786 (a1 : M → M)  : (∀ z0 : M, (t10 (M := M) (t43 (M := M) z0 (fun x1_1 : M => (a1 x1_1))) (a1 z0))) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a1 u1))
  let e1  : Prop := (t6)
  let e2 (u0 : M) (u1 : M) : Prop := (t14 (M := M) u1 (fun x0_1 : M => (e0 u0 x0_1)))
  let e3 (u0 : M) (u1 : M) : Prop := (t3 (e2 u0 u1) (e0 u0 u1))
  let e4 (u0 : M) : M := (t43 (M := M) u0 (fun x0_1 : M => (a1 x0_1)))
  let e5 (u0 : M) : Prop := (t10 (M := M) (e4 u0) (a1 u0))
  let e6 (u0 : M) : Prop := (t0 (e1) (e5 u0))
  have v0 := fun z0 : M => fun z1 : M => p533 (M := M) (fun w0 : M => (e0 z0 w0)) z1
  have v1 := fun z0 : M => fun z1 : M => p4 (e1) (e3 z0 z1) (v0 z0 z1)
  have v2 := fun z0 : M => p751 (M := M) (e1) (a1 z0) (fun w2 : M => (e2 w2 z0)) ((fun w2 : M => v1 w2 z0))
  have v3 : (∀ z0 : M, (e6 z0)) := (show (∀ z0 : M, (e6 z0)) from v2)
  have v4 := fun z0 : M => p318 (e5 z0) (v3 z0)
  exact v4
-- Actual MMB 787 nfnlem
theorem p787 (a2 : M → M) (a3 : M → M) (a4 : M → M) (h0 : (∀ z0 : M, (∀ z1 : M, (t0 (t10 (M := M) z1 (a3 z0)) (t10 (M := M) (a2 z1) (a4 z0)))))) (h1 : (t24 (M := M) (fun x0_0 : M => (a3 x0_0)))) : (t24 (M := M) (fun x0_0 : M => (a4 x0_0))) := by
  let e0 (u0 : M) : M := (t43 (M := M) (a3 u0) (fun x0_1 : M => (a2 x0_1)))
  let e1 (u0 : M) : Prop := (t10 (M := M) (e0 u0) (a4 u0))
  let e2 (u0 : M) : Prop := (t10 (M := M) (a4 u0) (e0 u0))
  have v0 := fun z0 : M => p341 (M := M) (e0 z0) (a4 z0)
  have v1 := fun z0 : M => p782 (M := M) (a3 z0) (fun w0 : M => (a2 w0)) (a4 z0) ((fun w0 : M => h0 z0 w0))
  have v2 := fun z0 : M => b3 (e1 z0) (e2 z0) (v0 z0) (v1 z0)
  have v3 := fun z0 : M => p674 (M := M) (a2 z0)
  have v4 := p776 (M := M) (fun w0 : M => (fun w1 : M => (a3 w0))) (fun w0 : M => (fun w1 : M => (a2 w1))) ((fun w1 : M => h1)) ((fun w1 : M => v3 w1)) 0
  have v5 := p687 (M := M) (fun w0 : M => (a4 w0)) (fun w0 : M => (e0 w0)) ((fun w0 : M => v2 w0)) (v4)
  exact v5
-- Actual MMB 788 nfnlem2
theorem p788 (a3 : M → M → M) (a4 : M → M) (a5 : M → M) (a6 : M → M) (h0 : (∀ z0 : M, (∀ z1 : M, (∀ z2 : M, (t0 (t2 (t10 (M := M) z1 (a4 z0)) (t10 (M := M) z2 (a5 z0))) (t10 (M := M) (a3 z1 z2) (a6 z0))))))) (h1 : (t24 (M := M) (fun x0_0 : M => (a4 x0_0)))) (h2 : (t24 (M := M) (fun x0_0 : M => (a5 x0_0)))) : (t24 (M := M) (fun x0_0 : M => (a6 x0_0))) := by
  let e0 (u0 : M) (u1 : M) : M := (t43 (M := M) (a5 u0) (fun x0_1 : M => (a3 u1 x0_1)))
  let e1 (u0 : M) : M := (t43 (M := M) (a4 u0) (fun x0_1 : M => (e0 u0 x0_1)))
  let e2 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 (a4 u0))
  let e3 (u0 : M) : Prop := (t10 (M := M) (e1 u0) (a6 u0))
  let e4 (u0 : M) : Prop := (t10 (M := M) (a6 u0) (e1 u0))
  have v0 := fun z0 : M => p341 (M := M) (e1 z0) (a6 z0)
  have v1 := fun z0 : M => fun z1 : M => p783 (M := M) (e2 z0 z1) (a5 z0) (fun w1 : M => (a3 z1 w1)) (a6 z0) ((fun w1 : M => h0 z0 z1 w1))
  have v2 := fun z0 : M => p782 (M := M) (a4 z0) (fun w0 : M => (e0 z0 w0)) (a6 z0) ((fun w0 : M => v1 z0 w0))
  have v3 := fun z0 : M => b3 (e3 z0) (e4 z0) (v0 z0) (v2 z0)
  have v4 := fun z0 : M => fun z1 : M => p674 (M := M) (a3 z0 z1)
  have v5 := fun z0 : M => p776 (M := M) (fun w0 : M => (fun w1 : M => (a5 w0))) (fun w0 : M => (fun w1 : M => (a3 z0 w1))) ((fun w1 : M => h2)) ((fun w1 : M => v4 z0 w1)) 0
  have v6 := p776 (M := M) (fun w0 : M => (fun w1 : M => (a4 w0))) (fun w0 : M => (fun w1 : M => (e0 w0 w1))) ((fun w1 : M => h1)) ((fun w1 : M => v5 w1)) 0
  have v7 := p687 (M := M) (fun w0 : M => (a6 w0)) (fun w0 : M => (e1 w0)) ((fun w0 : M => v3 w0)) (v6)
  exact v7
-- Actual MMB 789 nfsuc
theorem p789 (a1 : M → M) (h0 : (t24 (M := M) (fun x0_0 : M => (a1 x0_0)))) : (t24 (M := M) (fun x0_0 : M => (t29 (M := M) (a1 x0_0)))) := by
  let e0 (u0 : M) : M := (t29 (M := M) u0)
  let e1 (u0 : M) : M := (t29 (M := M) (a1 u0))
  have v0 := fun z0 : M => fun z1 : M => p739 (M := M) z0 (a1 z1)
  have v1 := p787 (M := M) (fun w1 : M => (e0 w1)) (fun w0 : M => (a1 w0)) (fun w0 : M => (e1 w0)) ((fun w0 : M => (fun w1 : M => v0 w1 w0))) (h0)
  exact v1
-- Actual MMB 796 addeqd
theorem p796 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) (h1 : (t0 (a0) (t10 (M := M) (a3) (a4)))) : (t0 (a0) (t10 (M := M) (t44 (M := M) (a1) (a3)) (t44 (M := M) (a2) (a4)))) := by
  have v0 := b790 (M := M) (a1) (a2) (a3) (a4)
  have v1 := p15 (a0) ((show Prop from (t10 (M := M) (a1) (a2)))) ((show Prop from (t10 (M := M) (a3) (a4)))) ((show Prop from (t10 (M := M) ((show M from (t44 (M := M) (a1) (a3)))) ((show M from (t44 (M := M) (a2) (a4))))))) (v0) (h0) (h1)
  exact v1
-- Actual MMB 797 muleqd
theorem p797 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) (h1 : (t0 (a0) (t10 (M := M) (a3) (a4)))) : (t0 (a0) (t10 (M := M) (t45 (M := M) (a1) (a3)) (t45 (M := M) (a2) (a4)))) := by
  have v0 := b791 (M := M) (a1) (a2) (a3) (a4)
  have v1 := p15 (a0) ((show Prop from (t10 (M := M) (a1) (a2)))) ((show Prop from (t10 (M := M) (a3) (a4)))) ((show Prop from (t10 (M := M) ((show M from (t45 (M := M) (a1) (a3)))) ((show M from (t45 (M := M) (a2) (a4))))))) (v0) (h0) (h1)
  exact v1
-- Actual MMB 798 addeq1d
theorem p798 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) : (t0 (a0) (t10 (M := M) (t44 (M := M) (a1) (a3)) (t44 (M := M) (a2) (a3)))) := by
  have v0 := p354 (M := M) (a0) (a3)
  have v1 := p796 (M := M) (a0) (a1) (a2) (a3) (a3) (h0) (v0)
  exact v1
-- Actual MMB 799 addeq1
theorem p799 (a0 : M) (a1 : M) (a2 : M)  : (t0 (t10 (M := M) (a0) (a1)) (t10 (M := M) (t44 (M := M) (a0) (a2)) (t44 (M := M) (a1) (a2)))) := by
  let e0  : Prop := (t10 (M := M) (a0) (a1))
  have v0 := p8 (e0)
  have v1 := p798 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 800 addeq2d
theorem p800 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (t0 (a0) (t10 (M := M) (a2) (a3)))) : (t0 (a0) (t10 (M := M) (t44 (M := M) (a1) (a2)) (t44 (M := M) (a1) (a3)))) := by
  have v0 := p354 (M := M) (a0) (a1)
  have v1 := p796 (M := M) (a0) (a1) (a1) (a2) (a3) (v0) (h0)
  exact v1
-- Actual MMB 801 addeq2
theorem p801 (a0 : M) (a1 : M) (a2 : M)  : (t0 (t10 (M := M) (a1) (a2)) (t10 (M := M) (t44 (M := M) (a0) (a1)) (t44 (M := M) (a0) (a2)))) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  have v0 := p8 (e0)
  have v1 := p800 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 802 muleq1d
theorem p802 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) : (t0 (a0) (t10 (M := M) (t45 (M := M) (a1) (a3)) (t45 (M := M) (a2) (a3)))) := by
  have v0 := p354 (M := M) (a0) (a3)
  have v1 := p797 (M := M) (a0) (a1) (a2) (a3) (a3) (h0) (v0)
  exact v1
-- Actual MMB 803 muleq1
theorem p803 (a0 : M) (a1 : M) (a2 : M)  : (t0 (t10 (M := M) (a0) (a1)) (t10 (M := M) (t45 (M := M) (a0) (a2)) (t45 (M := M) (a1) (a2)))) := by
  let e0  : Prop := (t10 (M := M) (a0) (a1))
  have v0 := p8 (e0)
  have v1 := p802 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 804 muleq2d
theorem p804 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (t0 (a0) (t10 (M := M) (a2) (a3)))) : (t0 (a0) (t10 (M := M) (t45 (M := M) (a1) (a2)) (t45 (M := M) (a1) (a3)))) := by
  have v0 := p354 (M := M) (a0) (a1)
  have v1 := p797 (M := M) (a0) (a1) (a1) (a2) (a3) (v0) (h0)
  exact v1
-- Actual MMB 805 muleq2
theorem p805 (a0 : M) (a1 : M) (a2 : M)  : (t0 (t10 (M := M) (a1) (a2)) (t10 (M := M) (t45 (M := M) (a0) (a1)) (t45 (M := M) (a0) (a2)))) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  have v0 := p8 (e0)
  have v1 := p804 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 806 nfadd

end ZF209.MM0ModelReplay
