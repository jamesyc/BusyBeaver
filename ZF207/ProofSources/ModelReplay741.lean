module
public import PropositionalReplay
public import ModelFormulaCertificates
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def t0 := fun (p q : Prop) => p → q
def t1 := fun (p : Prop) => ¬ p
def t6 := True
def t8 := fun (p : M → Prop) => ∀ x,p x
noncomputable def t9 (a1 : M → Prop)  : Prop := (t1 (t8 (M := M) (fun x1_0 : M => (t1 (a1 x1_0)))))
def t10 := fun (a b : M) => a=b
noncomputable def t2 (a0 : Prop) (a1 : Prop)  : Prop := (t1 (t0 (a0) (t1 (a1))))
noncomputable def t3 (a0 : Prop) (a1 : Prop)  : Prop := (t2 (t0 (a0) (a1)) (t0 (a1) (a0)))
def t16 := fun (a : M) (A : M → Prop) => A a
def t15 := fun (p : M → Prop) => p
noncomputable def t14 (a0 : M) (a2 : M → Prop)  : Prop := (t8 (M := M) (fun x0_0 : M => (t0 (t10 (M := M) x0_0 (a0)) (t8 (M := M) (fun x2_0 : M => (t0 (t10 (M := M) x2_0 x0_0) (a2 x2_0)))))))
noncomputable def t13 (a0 : M) (a1 : M)  : Prop := (t1 (t10 (M := M) (a0) (a1)))
def t29 := (fun x : M => x+1)
def t28 := (0 : M)
noncomputable def t4 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t1 (a0)) (a1))
noncomputable def t5 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t4 (t2 (a0) (a1)) (t2 (t1 (a0)) (a2)))
noncomputable def t7   : Prop := (t1 (t6))
noncomputable def t11 (a1 : M → Prop)  : Prop := (t8 (M := M) (fun x0_0 : M => (t0 (a1 x0_0) (t8 (M := M) (fun x2_0 : M => (a1 x2_0))))))
noncomputable def t17 (a0 : (M → Prop)) (a1 : (M → Prop))  : Prop := (t8 (M := M) (fun x0_0 : M => (t3 (t16 (M := M) x0_0 (a0)) (t16 (M := M) x0_0 (a1)))))
noncomputable def t18 (a0 : (M → Prop)) (a1 : (M → Prop))  : Prop := (t8 (M := M) (fun x0_0 : M => (t0 (t16 (M := M) x0_0 (a0)) (t16 (M := M) x0_0 (a1)))))
noncomputable def t19 (a0 : (M → Prop)) (a1 : (M → Prop))  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (t2 (t16 (M := M) x0_0 (a0)) (t16 (M := M) x0_0 (a1)))))
noncomputable def t20 (a0 : (M → Prop)) (a1 : (M → Prop))  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (t4 (t16 (M := M) x0_0 (a0)) (t16 (M := M) x0_0 (a1)))))
noncomputable def t22   : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (t6)))
noncomputable def t23 (a1 : M → (M → Prop))  : Prop := (t8 (M := M) (fun x0_0 : M => (t11 (M := M) (fun x1_0 : M => (t16 (M := M) x0_0 (a1 x1_0))))))
noncomputable def t24 (a1 : M → M)  : Prop := (t8 (M := M) (fun x0_0 : M => (t11 (M := M) (fun x1_0 : M => (t10 (M := M) x0_0 (a1 x1_0))))))
noncomputable def t25 (a0 : M) (a2 : M → (M → Prop))  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (t14 (M := M) (a0) (fun x1_1 : M => (t16 (M := M) x0_0 (a2 x1_1))))))
noncomputable def t30   : M := (t29 (M := M) (t28 (M := M)))
noncomputable def t31   : M := (t29 (M := M) (t30 (M := M)))
noncomputable def g0 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a0) (t0 (a1) (a0)))
noncomputable def g1 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t0 (a0) (t0 (a1) (a2))) (t0 (t0 (a0) (a1)) (t0 (a0) (a2))))
noncomputable def g2 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t0 (t1 (a0)) (t1 (a1))) (t0 (a1) (a0)))
noncomputable def g3 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a0) (a1))
noncomputable def g4 (a0 : Prop) (a1 : Prop)  : Prop := (a0)
noncomputable def g5 (a0 : Prop) (a1 : Prop)  : Prop := (a1)
noncomputable def g6   : Prop := (t6)
noncomputable def g7 (a1 : M → Prop) (z0 : M) : Prop := (a1 z0)
noncomputable def g8 (a1 : M → Prop)  : Prop := (t8 (M := M) (fun x0_0 : M => (a1 x0_0)))
noncomputable def g9 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (t0 (a1 x1_0) (a2 x1_0)))) (t0 (t8 (M := M) (fun x2_0 : M => (a1 x2_0))) (t8 (M := M) (fun x2_0 : M => (a2 x2_0)))))
noncomputable def g10 (a1 : Prop)  : Prop := (t0 (a1) (t8 (M := M) (fun x1_0 : M => (a1))))
noncomputable def g11 (a0 : M)  : Prop := (t9 (M := M) (fun x0_0 : M => (t10 (M := M) x0_0 (a0))))
noncomputable def g12 (a0 : M) (a1 : M) (a2 : M)  : Prop := (t0 (t10 (M := M) (a0) (a1)) (t0 (t10 (M := M) (a0) (a2)) (t10 (M := M) (a1) (a2))))
noncomputable def g13 (a1 : M → Prop)  : Prop := (t0 (t1 (t8 (M := M) (fun x2_0 : M => (a1 x2_0)))) (t8 (M := M) (fun x1_0 : M => (t1 (t8 (M := M) (fun x3_0 : M => (a1 x3_0)))))))
noncomputable def g14 (a2 : M → M → Prop)  : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (t8 (M := M) (fun x2_0 : M => (a2 x1_0 x2_0))))) (t8 (M := M) (fun x1_0 : M => (t8 (M := M) (fun x2_0 : M => (a2 x2_0 x1_0))))))
noncomputable def g15 (a1 : M) (a2 : M → Prop) (z0 : M) : Prop := (t0 (t10 (M := M) z0 (a1)) (t0 (a2 z0) (t8 (M := M) (fun x2_0 : M => (t0 (t10 (M := M) x2_0 (a1)) (a2 x2_0))))))
noncomputable def g16 (a0 : M) (a2 : M → Prop)  : Prop := (t3 (t16 (M := M) (a0) (t15 (M := M) (fun x2_0 : M => (a2 x2_0)))) (t14 (M := M) (a0) (fun x1_1 : M => (a2 x1_1))))
noncomputable def g17 (a0 : M) (a1 : M) (a2 : (M → Prop))  : Prop := (t0 (t10 (M := M) (a0) (a1)) (t0 (t16 (M := M) (a0) (a2)) (t16 (M := M) (a1) (a2))))
noncomputable def g18 (a0 : M)  : Prop := (t13 (M := M) (t29 (M := M) (a0)) (t28 (M := M)))
noncomputable def g19 (a0 : M) (a1 : M)  : Prop := (t3 (t10 (M := M) (t29 (M := M) (a0)) (t29 (M := M) (a1))) (t10 (M := M) (a0) (a1)))
noncomputable def g20 (a1 : M → Prop)  : Prop := (t0 (t14 (M := M) (t28 (M := M)) (fun x1_1 : M => (a1 x1_1))) (t0 (t8 (M := M) (fun x2_0 : M => (t0 (a1 x2_0) (t14 (M := M) (t29 (M := M) x2_0) (fun x4_1 : M => (a1 x4_1)))))) (t8 (M := M) (fun x2_0 : M => (a1 x2_0)))))
noncomputable def g21 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t0 (a1) (a2)))
noncomputable def g22 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t0 (a0) (a1)) (t0 (a0) (a2)))
noncomputable def g23 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (a1))
noncomputable def g24 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (a2))
noncomputable def g25 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (a1)
noncomputable def g26 (a0 : Prop)  : Prop := (t0 (a0) (a0))
noncomputable def g28 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a1) (a2))
noncomputable def g29 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t0 (a2) (a1)))
noncomputable def g30 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t0 (a1) (t0 (a2) (a3))))
noncomputable def g31 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t0 (t0 (a1) (a2)) (t0 (a1) (a3))))
noncomputable def g32 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t0 (t1 (a1)) (t1 (a2))))
noncomputable def g33 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a1) (t0 (a2) (a3)))
noncomputable def g34 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (a1))
noncomputable def g35 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (a2))
noncomputable def g36 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (a3))
noncomputable def g37 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t0 (a1) (a2)))
noncomputable def g38 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t0 (a2) (a3)))
noncomputable def g39 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t0 (a1) (a3)))
noncomputable def g40 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a1) (a2))
noncomputable def g41 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a2) (a3))
noncomputable def g42 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t0 (a1) (a2)) (t0 (t0 (a0) (a1)) (t0 (a0) (a2))))
noncomputable def g43 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t1 (a0)) (t0 (a0) (a1)))
noncomputable def g44 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a1) (t0 (a0) (a2)))
noncomputable def g45 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a0) (t0 (t0 (a0) (a1)) (a1)))
noncomputable def g48 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a0) (t0 (t1 (a0)) (a1)))
noncomputable def g50 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t0 (a1) (a2)) (t0 (a0) (a2)))
noncomputable def g51 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t0 (t0 (a2) (a3)) (t0 (a1) (a3))))
noncomputable def g52 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t0 (a0) (t0 (a1) (a2)))
noncomputable def g53 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t0 (a0) (t0 (a3) (a4)))
noncomputable def g56 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t0 (a0) (t0 (a0) (a1))) (t0 (a0) (a1)))
noncomputable def g58 (a0 : Prop)  : Prop := (t0 (t0 (t1 (a0)) (a0)) (a0))
noncomputable def g60 (a0 : Prop)  : Prop := (t0 (t0 (a0) (t1 (a0))) (t1 (a0)))
noncomputable def g61 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t0 (a0) (t1 (a1))) (t0 (a1) (t1 (a0))))
noncomputable def g62 (a0 : Prop)  : Prop := (t0 (a0) (t1 (t1 (a0))))
noncomputable def g63 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t0 (a0) (a1)) (t0 (t1 (a1)) (t1 (a0))))
noncomputable def g64 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t0 (t1 (a0)) (a1)) (t0 (t1 (a1)) (a0)))
noncomputable def g65 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t1 (a0)) (a1))
noncomputable def g66 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t0 (t1 (a1)) (a2)))
noncomputable def g67 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t0 (t1 (a2)) (a1)))
noncomputable def g70 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t0 (t1 (a2)) (t1 (a1))))
noncomputable def g71 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a1) (a0))
noncomputable def g72 (a0 : Prop) (a1 : Prop)  : Prop := (t1 (a0))
noncomputable def g73 (a0 : Prop) (a1 : Prop)  : Prop := (t1 (a1))
noncomputable def g75 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t1 (a1)))
noncomputable def g76 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t1 (a2)))
noncomputable def g77 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t1 (a1))
noncomputable def g78 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t2 (a0) (a1)) (a0))
noncomputable def g79 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t2 (a0) (a1)) (a1))
noncomputable def g81 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a0) (t0 (a1) (t2 (a0) (a1))))
noncomputable def g82 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t2 (a1) (a2)))
noncomputable def g83 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t2 (a0) (a1)) (a2))
noncomputable def g84 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t2 (t2 (a0) (a1)) (a2)) (a0))
noncomputable def g85 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t2 (t2 (a0) (a1)) (a2)) (a1))
noncomputable def g86 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t2 (a0) (t2 (a1) (a2))) (a1))
noncomputable def g87 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t2 (a0) (t2 (a1) (a2))) (a2))
noncomputable def g88 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t2 (t2 (a0) (a1)) (a2)) (a3))
noncomputable def g89 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t0 (a0) (a4))
noncomputable def g90 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t0 (t2 (t2 (t2 (a0) (a1)) (a2)) (a3)) (a4))
noncomputable def g99 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t2 (t2 (t2 (a0) (a1)) (a2)) (a3)) (a1))
noncomputable def g100 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t2 (t2 (t2 (a0) (a1)) (a2)) (a3)) (a0))
noncomputable def g108 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t2 (a1) (a0)) (a2))
noncomputable def g109 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t0 (a1) (a2)) (a3))
noncomputable def g110 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t2 (a0) (a1)) (a2))
noncomputable def g111 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t2 (a1) (a2)) (a3))
noncomputable def g112 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t0 (a0) (t0 (t2 (a1) (a3)) (t2 (a2) (a4))))
noncomputable def g114 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t0 (t2 (a1) (a2)) (t2 (a1) (a3))))
noncomputable def g115 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t0 (a0) (a1)) (t0 (t2 (a0) (a2)) (t2 (a1) (a2))))
noncomputable def g116 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t0 (a1) (a2)) (t0 (t2 (a0) (a1)) (t2 (a0) (a2))))
noncomputable def g120 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t2 (t2 (a0) (a2)) (a1)) (a3))
noncomputable def g122 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t2 (a0) (t1 (a1))) (a2))
noncomputable def g125 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t2 (a0) (a2)) (a1))
noncomputable def g126 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t3 (a0) (a1)) (t0 (a0) (a1)))
noncomputable def g127 (a0 : Prop) (a1 : Prop)  : Prop := (t3 (a0) (a1))
noncomputable def g128 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t3 (a1) (a2)))
noncomputable def g129 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t3 (a0) (a1)) (t0 (a1) (a0)))
noncomputable def g130 (a0 : Prop)  : Prop := (t3 (a0) (a0))
noncomputable def g131 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a0) (t3 (a1) (a1)))
noncomputable def g132 (a0 : Prop) (a1 : Prop)  : Prop := (t3 (a1) (a0))
noncomputable def g133 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t3 (a2) (a1)))
noncomputable def g135 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t3 (a0) (t1 (a1))) (t3 (a1) (t1 (a0))))
noncomputable def g136 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t3 (a0) (a1)) (t3 (t1 (a0)) (t1 (a1))))
noncomputable def g137 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t3 (t1 (a0)) (t1 (a1))) (t3 (a0) (a1)))
noncomputable def g144 (a0 : Prop)  : Prop := (t3 (a0) (t1 (t1 (a0))))
noncomputable def g145 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a0) (t0 (a1) (t3 (a0) (a1))))
noncomputable def g146 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t1 (a0)) (t0 (t1 (a1)) (t3 (a0) (a1))))
noncomputable def g147 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t3 (a0) (a1)) (t3 (a1) (a0)))
noncomputable def g149 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (a1) (a2)))
noncomputable def g150 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (a2) (a3)))
noncomputable def g151 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (a1) (a3)))
noncomputable def g153 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (a2) (a1)))
noncomputable def g154 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (a3) (a2)))
noncomputable def g155 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t3 (a0) (a1)) (t0 (t3 (a1) (a2)) (t3 (a0) (a2))))
noncomputable def g157 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t3 (a1) (a0)) (t0 (t3 (a1) (a2)) (t3 (a0) (a2))))
noncomputable def g158 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t3 (a0) (a1)) (t0 (t3 (a2) (a1)) (t3 (a0) (a2))))
noncomputable def g159 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (a1) (a2))
noncomputable def g160 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (a2) (a1))
noncomputable def g161 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (a0) (a1))
noncomputable def g162 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (a1) (a0))
noncomputable def g163 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t3 (a1) (a2))
noncomputable def g164 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t3 (a2) (a1))
noncomputable def g165 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t3 (a2) (a3))
noncomputable def g166 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t3 (a3) (a2))
noncomputable def g167 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a2) (t3 (a1) (a3)))
noncomputable def g168 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t0 (a2) (a1)))
noncomputable def g171 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t0 (a0) (t3 (a1) (a2)))
noncomputable def g172 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t0 (a0) (t3 (a3) (a4)))
noncomputable def g173 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t3 (a3) (a1))
noncomputable def g174 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t3 (a4) (a2))
noncomputable def g177 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t3 (a0) (a1))
noncomputable def g178 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t3 (a2) (a0))
noncomputable def g179 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t3 (a3) (a1))
noncomputable def g180 (a0 : Prop) (a1 : Prop)  : Prop := (t3 (t2 (a0) (a1)) (t2 (a1) (a0)))
noncomputable def g183 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t0 (a1) (a0)) (t3 (t2 (a0) (a1)) (a1)))
noncomputable def g184 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a0) (t3 (t2 (a0) (a1)) (a1)))
noncomputable def g185 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a1) (t3 (t2 (a0) (a1)) (a0)))
noncomputable def g189 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t3 (t1 (a1)) (t1 (a2))))
noncomputable def g190 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t0 (a0) (t3 (t0 (a1) (a3)) (t0 (a2) (a4))))
noncomputable def g193 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (t0 (a1) (a3)) (t0 (a2) (a3))))
noncomputable def g194 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (t0 (a1) (a2)) (t0 (a1) (a3))))
noncomputable def g195 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (t0 (a0) (a2)) (t0 (a1) (a2)))
noncomputable def g196 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (t0 (a0) (a1)) (t0 (a0) (a2)))
noncomputable def g197 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t3 (t0 (a0) (a2)) (t0 (a1) (a3)))
noncomputable def g198 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t0 (a0) (t3 (t2 (a1) (a3)) (t2 (a2) (a4))))
noncomputable def g201 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t2 (a0) (a1)) (t3 (a2) (a3)))
noncomputable def g202 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (t2 (a1) (a3)) (t2 (a2) (a3))))
noncomputable def g203 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (t2 (a1) (a2)) (t2 (a1) (a3))))
noncomputable def g204 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t3 (a0) (a1)) (t0 (t3 (a2) (a3)) (t3 (t2 (a0) (a2)) (t2 (a1) (a3)))))
noncomputable def g205 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (t2 (a0) (a2)) (t2 (a1) (a2)))
noncomputable def g206 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (t2 (a0) (a1)) (t2 (a0) (a2)))
noncomputable def g207 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t0 (a0) (t3 (a1) (a2))) (t3 (t2 (a0) (a1)) (t2 (a0) (a2))))
noncomputable def g208 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t0 (a2) (t3 (a0) (a1))) (t3 (t2 (a0) (a2)) (t2 (a1) (a2))))
noncomputable def g233 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t2 (a0) (a2)) (a1))
noncomputable def g234 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t2 (a0) (a3)) (a1))
noncomputable def g235 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a1) (a0))
noncomputable def g236 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a2) (a0))
noncomputable def g237 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t0 (a0) (t3 (t3 (a1) (a3)) (t3 (a2) (a4))))
noncomputable def g238 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (t3 (a1) (a3)) (t3 (a2) (a3))))
noncomputable def g239 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (t3 (a1) (a2)) (t3 (a1) (a3))))
noncomputable def g240 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t3 (a0) (a1)) (t0 (t3 (a2) (a3)) (t3 (t3 (a0) (a2)) (t3 (a1) (a3)))))
noncomputable def g242 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t3 (a1) (a2)) (t3 (t3 (a0) (a1)) (t3 (a0) (a2))))
noncomputable def g243 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (t0 (t2 (a0) (a1)) (a2)) (t0 (a0) (t0 (a1) (a2))))
noncomputable def g246 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop)  : Prop := (t0 (a0) (t3 (t4 (a1) (a3)) (t4 (a2) (a4))))
noncomputable def g247 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t3 (a0) (a1)) (t0 (t3 (a2) (a3)) (t3 (t4 (a0) (a2)) (t4 (a1) (a3)))))
noncomputable def g248 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (t4 (a1) (a3)) (t4 (a2) (a3))))
noncomputable def g249 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t3 (a0) (a1)) (t3 (t4 (a0) (a2)) (t4 (a1) (a2))))
noncomputable def g250 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t3 (t4 (a1) (a2)) (t4 (a1) (a3))))
noncomputable def g252 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a0) (t4 (a0) (a1)))
noncomputable def g253 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a1) (t4 (a0) (a1)))
noncomputable def g255 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (a0) (t0 (t4 (a1) (a2)) (a3)))
noncomputable def g256 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t2 (a0) (a1)) (a3))
noncomputable def g257 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t0 (t2 (a0) (a2)) (a3))
noncomputable def g258 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t4 (a1) (a2)))
noncomputable def g259 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t0 (a0) (a2)) (t0 (t0 (a1) (a2)) (t0 (t4 (a0) (a1)) (a2))))
noncomputable def g265 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (t4 (a0) (a2)) (t4 (a1) (a2)))
noncomputable def g266 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (t4 (a0) (a1)) (t4 (a0) (a2)))
noncomputable def g268 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : Prop := (t3 (t4 (a0) (a2)) (t4 (a1) (a3)))
noncomputable def g269 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t4 (a0) (a1)) (t4 (a1) (a0)))
noncomputable def g270 (a0 : Prop) (a1 : Prop)  : Prop := (t3 (t4 (a0) (a1)) (t4 (a1) (a0)))
noncomputable def g275 (a0 : Prop) (a1 : Prop)  : Prop := (t3 (t1 (t2 (a0) (a1))) (t0 (a0) (t1 (a1))))
noncomputable def g277 (a0 : Prop) (a1 : Prop)  : Prop := (t3 (t1 (t4 (a0) (a1))) (t2 (t1 (a0)) (t1 (a1))))
noncomputable def g280 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (t2 (a0) (t4 (a1) (a2))) (t4 (t2 (a0) (a1)) (t2 (a0) (a2))))
noncomputable def g281 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t3 (t2 (t4 (a0) (a1)) (a2)) (t4 (t2 (a0) (a2)) (t2 (a1) (a2))))
noncomputable def g290 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (a0) (t3 (t0 (a0) (a1)) (a1)))
noncomputable def g293 (a0 : Prop) (a1 : Prop)  : Prop := (t0 (t1 (a1)) (t3 (t4 (a0) (a1)) (a0)))
noncomputable def g298 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop)  : Prop := (t0 (a0) (t3 (a1) (a2)))
noncomputable def g299 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop)  : Prop := (t0 (a0) (t3 (a3) (a4)))
noncomputable def g300 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop)  : Prop := (t0 (a0) (t3 (a5) (a6)))
noncomputable def g301 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop)  : Prop := (t0 (a0) (t3 (t5 (a1) (a3) (a5)) (t5 (a2) (a4) (a6))))
noncomputable def g310 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (a0) (t3 (t5 (a0) (a1) (a2)) (a1)))
noncomputable def g311 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : Prop := (t0 (t1 (a0)) (t3 (t5 (a0) (a1) (a2)) (a2)))
noncomputable def g327 (a0 : Prop)  : Prop := (t0 (t6) (a0))
noncomputable def g328 (a0 : Prop)  : Prop := (a0)
noncomputable def g330   : Prop := (t1 (t7))
noncomputable def g333 (a0 : Prop)  : Prop := (t3 (t3 (a0) (t7)) (t1 (a0)))
noncomputable def g335 (a0 : M) (a1 : M) (a2 : M)  : Prop := (t0 (t10 (M := M) (a1) (a0)) (t0 (t10 (M := M) (a1) (a2)) (t10 (M := M) (a0) (a2))))
noncomputable def g336 (a1 : M → Prop) (a2 : M → Prop) (z0 : M) : Prop := (t0 (a1 z0) (a2 z0))
noncomputable def g337 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (a1 x1_0))) (t8 (M := M) (fun x1_0 : M => (a2 x1_0))))
noncomputable def g338 (a1 : Prop) (a2 : M → Prop) (z0 : M) : Prop := (t0 (a1) (a2 z0))
noncomputable def g339 (a1 : Prop) (a2 : M → Prop)  : Prop := (t0 (a1) (t8 (M := M) (fun x1_0 : M => (a2 x1_0))))
noncomputable def g340 (a1 : M → Prop) (a2 : Prop) (z0 : M) : Prop := (t0 (a1 z0) (a2))
noncomputable def g341 (a1 : M → Prop) (a2 : Prop)  : Prop := (t0 (t9 (M := M) (fun x1_0 : M => (a1 x1_0))) (a2))
noncomputable def g342 (a0 : M)  : Prop := (t10 (M := M) (a0) (a0))
noncomputable def g343 (a0 : M) (a1 : M)  : Prop := (t0 (t10 (M := M) (a0) (a1)) (t10 (M := M) (a1) (a0)))
noncomputable def g344 (a0 : M) (a1 : M) (a2 : M)  : Prop := (t0 (t10 (M := M) (a0) (a1)) (t0 (t10 (M := M) (a1) (a2)) (t10 (M := M) (a0) (a2))))
noncomputable def g346 (a0 : M) (a1 : M) (a2 : M)  : Prop := (t0 (t10 (M := M) (a0) (a1)) (t0 (t10 (M := M) (a2) (a1)) (t10 (M := M) (a0) (a2))))
noncomputable def g347 (a0 : M) (a1 : M)  : Prop := (t3 (t10 (M := M) (a0) (a1)) (t10 (M := M) (a1) (a0)))
noncomputable def g348 (a0 : M) (a1 : M) (a2 : M)  : Prop := (t0 (t10 (M := M) (a0) (a1)) (t3 (t10 (M := M) (a0) (a2)) (t10 (M := M) (a1) (a2))))
noncomputable def g349 (a0 : M) (a1 : M) (a2 : M)  : Prop := (t0 (t10 (M := M) (a1) (a2)) (t3 (t10 (M := M) (a0) (a1)) (t10 (M := M) (a0) (a2))))
noncomputable def g350 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t0 (a0) (t10 (M := M) (a1) (a2)))
noncomputable def g351 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t0 (a0) (t3 (t10 (M := M) (a1) (a3)) (t10 (M := M) (a2) (a3))))
noncomputable def g352 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t0 (a0) (t10 (M := M) (a2) (a3)))
noncomputable def g353 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t0 (a0) (t3 (t10 (M := M) (a1) (a2)) (t10 (M := M) (a1) (a3))))
noncomputable def g354 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M)  : Prop := (t0 (a0) (t10 (M := M) (a1) (a2)))
noncomputable def g355 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M)  : Prop := (t0 (a0) (t10 (M := M) (a3) (a4)))
noncomputable def g356 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M)  : Prop := (t0 (a0) (t3 (t10 (M := M) (a1) (a3)) (t10 (M := M) (a2) (a4))))
noncomputable def g357 (a0 : M) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t0 (t10 (M := M) (a0) (a1)) (t0 (t10 (M := M) (a2) (a3)) (t3 (t10 (M := M) (a0) (a2)) (t10 (M := M) (a1) (a3)))))
noncomputable def g359 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t0 (a0) (t10 (M := M) (a2) (a1)))
noncomputable def g360 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t0 (a0) (t10 (M := M) (a1) (a3)))
noncomputable def g361 (a0 : Prop) (a1 : M)  : Prop := (t0 (a0) (t10 (M := M) (a1) (a1)))
noncomputable def g364 (a0 : Prop) (a1 : M) (a2 : M)  : Prop := (t0 (a0) (t10 (M := M) (a1) (a2)))
noncomputable def g365 (a0 : Prop) (a1 : M) (a2 : M)  : Prop := (t0 (a0) (t10 (M := M) (a2) (a1)))
noncomputable def g369 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t0 (a0) (t10 (M := M) (a3) (a2)))
noncomputable def g370 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t10 (M := M) (a1) (a2))
noncomputable def g371 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t10 (M := M) (a2) (a1))
noncomputable def g372 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t10 (M := M) (a2) (a3))
noncomputable def g373 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t10 (M := M) (a3) (a2))
noncomputable def g376 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M)  : Prop := (t10 (M := M) (a3) (a1))
noncomputable def g377 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M)  : Prop := (t10 (M := M) (a4) (a2))
noncomputable def g378 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (t3 (a1 x1_0) (a2 x1_0)))) (t3 (t8 (M := M) (fun x2_0 : M => (a1 x2_0))) (t8 (M := M) (fun x2_0 : M => (a2 x2_0)))))
noncomputable def g379 (a1 : M → Prop) (a2 : M → Prop) (z0 : M) : Prop := (t3 (a1 z0) (a2 z0))
noncomputable def g380 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t3 (t8 (M := M) (fun x1_0 : M => (a1 x1_0))) (t8 (M := M) (fun x1_0 : M => (a2 x1_0))))
noncomputable def g381 (a1 : Prop) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (a1) (t0 (a2 z0) (a3 z0)))
noncomputable def g382 (a1 : Prop) (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t0 (a1) (t0 (t8 (M := M) (fun x2_0 : M => (a2 x2_0))) (t8 (M := M) (fun x2_0 : M => (a3 x2_0)))))
noncomputable def g385 (a1 : M → Prop) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (a1 z0) (t0 (a2 z0) (a3 z0)))
noncomputable def g386 (a1 : M → Prop) (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (a1 x1_0))) (t0 (t8 (M := M) (fun x2_0 : M => (a2 x2_0))) (t8 (M := M) (fun x2_0 : M => (a3 x2_0)))))
noncomputable def g387 (a0 : Prop) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (a0) (t3 (a2 z0) (a3 z0)))
noncomputable def g388 (a0 : Prop) (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t0 (a0) (t3 (t8 (M := M) (fun x2_0 : M => (a2 x2_0))) (t8 (M := M) (fun x2_0 : M => (a3 x2_0)))))
noncomputable def g389 (a1 : Prop) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (t2 (a1) (a2 z0)) (a3 z0))
noncomputable def g390 (a1 : Prop) (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t0 (a1) (t8 (M := M) (fun x1_0 : M => (t0 (a2 x1_0) (a3 x1_0)))))
noncomputable def g391 (a2 : M → M → Prop)  : Prop := (t3 (t8 (M := M) (fun x1_0 : M => (t8 (M := M) (fun x2_0 : M => (a2 x1_0 x2_0))))) (t8 (M := M) (fun x1_0 : M => (t8 (M := M) (fun x2_0 : M => (a2 x2_0 x1_0))))))
noncomputable def g394 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (t0 (a1 x1_0) (a2 x1_0)))) (t0 (t9 (M := M) (fun x2_0 : M => (a1 x2_0))) (t9 (M := M) (fun x2_0 : M => (a2 x2_0)))))
noncomputable def g395 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t0 (t9 (M := M) (fun x1_0 : M => (a1 x1_0))) (t9 (M := M) (fun x1_0 : M => (a2 x1_0))))
noncomputable def g396 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (t3 (a1 x1_0) (a2 x1_0)))) (t3 (t9 (M := M) (fun x2_0 : M => (a1 x2_0))) (t9 (M := M) (fun x2_0 : M => (a2 x2_0)))))
noncomputable def g397 (a0 : Prop) (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t0 (a0) (t3 (t9 (M := M) (fun x2_0 : M => (a2 x2_0))) (t9 (M := M) (fun x2_0 : M => (a3 x2_0)))))
noncomputable def g398 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t3 (t9 (M := M) (fun x1_0 : M => (a1 x1_0))) (t9 (M := M) (fun x1_0 : M => (a2 x1_0))))
noncomputable def g400 (a1 : M → Prop) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (a1 z0) (t3 (a2 z0) (a3 z0)))
noncomputable def g404 (a1 : M → Prop) (z0 : M) : Prop := (t0 (a1 z0) (t9 (M := M) (fun x1_0 : M => (a1 x1_0))))
noncomputable def g407 (a1 : M → Prop)  : Prop := (t3 (t8 (M := M) (fun x1_0 : M => (t1 (a1 x1_0)))) (t1 (t9 (M := M) (fun x2_0 : M => (a1 x2_0)))))
noncomputable def g408 (a1 : M → Prop) (z0 : M) : Prop := (t1 (a1 z0))
noncomputable def g409 (a1 : M → Prop)  : Prop := (t1 (t9 (M := M) (fun x1_0 : M => (a1 x1_0))))
noncomputable def g410 (a1 : M → Prop)  : Prop := (t3 (t8 (M := M) (fun x1_0 : M => (a1 x1_0))) (t1 (t9 (M := M) (fun x2_0 : M => (t1 (a1 x2_0))))))
noncomputable def g411 (a1 : M → Prop)  : Prop := (t3 (t9 (M := M) (fun x1_0 : M => (t1 (a1 x1_0)))) (t1 (t8 (M := M) (fun x2_0 : M => (a1 x2_0)))))
noncomputable def g412 (a1 : M → Prop) (z0 : M) : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (a1 x1_0))) (a1 z0))
noncomputable def g418 (a1 : Prop) (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t0 (a1) (t0 (t9 (M := M) (fun x2_0 : M => (a2 x2_0))) (t9 (M := M) (fun x2_0 : M => (a3 x2_0)))))
noncomputable def g424 (a0 : Prop) (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t0 (a0) (t3 (t11 (M := M) (fun x2_0 : M => (a2 x2_0))) (t11 (M := M) (fun x2_0 : M => (a3 x2_0)))))
noncomputable def g425 (a0 : Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (a0)))
noncomputable def g426 (a1 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (a1 x0_0)))
noncomputable def g427 (a1 : M → Prop) (z0 : M) : Prop := (t0 (a1 z0) (t8 (M := M) (fun x1_0 : M => (a1 x1_0))))
noncomputable def g428 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t3 (t11 (M := M) (fun x1_0 : M => (a1 x1_0))) (t11 (M := M) (fun x1_0 : M => (a2 x1_0))))
noncomputable def g429 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (a2 x0_0)))
noncomputable def g430 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (a1 x0_0)))
noncomputable def g431 (a2 : M → M → Prop) (z0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a2 x0_0 z0)))
noncomputable def g432 (a2 : M → M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (t8 (M := M) (fun x1_0 : M => (a2 x0_0 x1_0)))))
noncomputable def g433 (a1 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (t1 (a1 x0_0))))
noncomputable def g434 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (t0 (a1 x0_0) (a2 x0_0))))
noncomputable def g435 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (t2 (a1 x0_0) (a2 x0_0))))
noncomputable def g436 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (t4 (a1 x0_0) (a2 x0_0))))
noncomputable def g437 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (t3 (a1 x0_0) (a2 x0_0))))
noncomputable def g438 (a1 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (t9 (M := M) (fun x1_0 : M => (a1 x1_0)))))
noncomputable def g439 (a2 : M → M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (t9 (M := M) (fun x1_0 : M => (a2 x0_0 x1_0)))))
noncomputable def g440 (a1 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (t8 (M := M) (fun x1_0 : M => (a1 x1_0)))))
noncomputable def g441 (a1 : M → Prop) (a2 : M → Prop) (z0 : M) : Prop := (t0 (a1 z0) (t8 (M := M) (fun x1_0 : M => (a2 x1_0))))
noncomputable def g442 (a1 : M → Prop) (a2 : M → Prop) (z0 : M) : Prop := (t0 (t9 (M := M) (fun x1_0 : M => (a1 x1_0))) (a2 z0))
noncomputable def g443 (a1 : M → Prop) (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (a1 x0_0)))
noncomputable def g444 (a1 : M → Prop) (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (a3 x0_0)))
noncomputable def g445 (a1 : M → Prop) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (a1 z0) (t0 (t9 (M := M) (fun x2_0 : M => (a2 x2_0))) (a3 z0)))
noncomputable def g447 (a1 : M → Prop) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (a1 z0) (t3 (t8 (M := M) (fun x2_0 : M => (a2 x2_0))) (t8 (M := M) (fun x2_0 : M => (a3 x2_0)))))
noncomputable def g448 (a1 : Prop) (a2 : M → Prop) (a3 : Prop) (z0 : M) : Prop := (t0 (a1) (t0 (a2 z0) (a3)))
noncomputable def g449 (a1 : Prop) (a2 : M → Prop) (a3 : Prop)  : Prop := (t0 (a1) (t0 (t9 (M := M) (fun x2_0 : M => (a2 x2_0))) (a3)))
noncomputable def g450 (a1 : Prop) (a2 : M → Prop) (a3 : Prop) (z0 : M) : Prop := (t0 (t2 (a1) (a2 z0)) (a3))
noncomputable def g451 (a1 : M → Prop) (a2 : Prop)  : Prop := (t3 (t0 (t9 (M := M) (fun x2_0 : M => (a1 x2_0))) (a2)) (t8 (M := M) (fun x1_0 : M => (t0 (a1 x1_0) (a2)))))
noncomputable def g453 (a1 : M) (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (a3 x0_0)))
noncomputable def g454 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (t10 (M := M) z0 (a1)) (t3 (a2 z0) (a3 z0)))
noncomputable def g455 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (a3 z0) (t9 (M := M) (fun x1_0 : M => (a2 x1_0))))
noncomputable def g456 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (a2 x1_0))) (a3 z0))
noncomputable def g468 (a1 : M) (a2 : M → Prop) (a3 : Prop) (z0 : M) : Prop := (t0 (t10 (M := M) z0 (a1)) (t3 (a2 z0) (a3)))
noncomputable def g469 (a1 : M) (a2 : M → Prop) (a3 : Prop)  : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (a2 x1_0))) (a3))
noncomputable def g470 (a1 : M) (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (a2 x0_0)))
noncomputable def g471 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (t2 (a2 z0) (t10 (M := M) z0 (a1))) (a3 z0))
noncomputable def g472 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (a2 z0) (t9 (M := M) (fun x1_0 : M => (a3 x1_0))))
noncomputable def g473 (a1 : Prop) (a2 : M) (a3 : M → Prop) (z0 : M) : Prop := (t0 (t2 (a1) (t10 (M := M) z0 (a2))) (a3 z0))
noncomputable def g474 (a1 : Prop) (a2 : M) (a3 : M → Prop)  : Prop := (t0 (a1) (t9 (M := M) (fun x1_0 : M => (a3 x1_0))))
noncomputable def g477 (a1 : M) (a2 : M → Prop) (z0 : M) : Prop := (t0 (t10 (M := M) z0 (a1)) (a2 z0))
noncomputable def g478 (a1 : M) (a2 : M → Prop)  : Prop := (t9 (M := M) (fun x0_0 : M => (a2 x0_0)))
noncomputable def g479 (a1 : M) (a2 : M → Prop) (a3 : Prop)  : Prop := (t0 (a3) (t9 (M := M) (fun x1_0 : M => (a2 x1_0))))
noncomputable def g480 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (a4 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (a2 x0_0)))
noncomputable def g481 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (a4 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (a4 x0_0)))
noncomputable def g482 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (a4 : M → Prop) (z0 : M) : Prop := (t0 (t2 (a2 z0) (t10 (M := M) z0 (a1))) (t0 (a3 z0) (a4 z0)))
noncomputable def g483 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (a4 : M → Prop) (z0 : M) : Prop := (t0 (a2 z0) (t0 (t8 (M := M) (fun x2_0 : M => (a3 x2_0))) (a4 z0)))
noncomputable def g487 (a0 : Prop) (a2 : Prop) (a3 : M) (a4 : M → Prop) (z0 : M) : Prop := (t0 (t2 (a2) (t10 (M := M) z0 (a3))) (t0 (a4 z0) (a0)))
noncomputable def g488 (a0 : Prop) (a2 : Prop) (a3 : M) (a4 : M → Prop)  : Prop := (t0 (a2) (t0 (t8 (M := M) (fun x2_0 : M => (a4 x2_0))) (a0)))
noncomputable def g489 (a1 : Prop) (a2 : M → Prop)  : Prop := (t3 (t9 (M := M) (fun x1_0 : M => (t2 (a1) (a2 x1_0)))) (t2 (a1) (t9 (M := M) (fun x2_0 : M => (a2 x2_0)))))
noncomputable def g490 (a1 : M → Prop) (a2 : Prop)  : Prop := (t3 (t9 (M := M) (fun x1_0 : M => (t2 (a1 x1_0) (a2)))) (t2 (t9 (M := M) (fun x2_0 : M => (a1 x2_0))) (a2)))
noncomputable def g529 (a2 : M → M → Prop) (a3 : M → M → Prop) (z0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a2 z0 x0_0)))
noncomputable def g530 (a2 : M → M → Prop) (a3 : M → M → Prop) (z0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a3 x0_0 z0)))
noncomputable def g531 (a2 : M → M → Prop) (a3 : M → M → Prop) (z0 : M) (z1 : M) : Prop := (t0 (t10 (M := M) z0 z1) (t3 (a2 z0 z1) (a3 z0 z1)))
noncomputable def g532 (a2 : M → M → Prop) (a3 : M → M → Prop) (z0 : M) (z1 : M) : Prop := (t3 (t8 (M := M) (fun x1_0 : M => (a2 x1_0 z1))) (t8 (M := M) (fun x1_0 : M => (a3 z0 x1_0))))
noncomputable def g533 (a2 : M → Prop) (a3 : M → Prop) (z0 : M) (z1 : M) : Prop := (t0 (t10 (M := M) z0 z1) (t3 (a2 z0) (a3 z1)))
noncomputable def g534 (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t3 (t8 (M := M) (fun x1_0 : M => (a2 x1_0))) (t8 (M := M) (fun x1_0 : M => (a3 x1_0))))
noncomputable def g535 (a2 : M → M → Prop) (a3 : M → M → Prop) (z0 : M) (z1 : M) : Prop := (t3 (t9 (M := M) (fun x1_0 : M => (a2 x1_0 z1))) (t9 (M := M) (fun x1_0 : M => (a3 z0 x1_0))))
noncomputable def g536 (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t3 (t9 (M := M) (fun x1_0 : M => (a2 x1_0))) (t9 (M := M) (fun x1_0 : M => (a3 x1_0))))
noncomputable def g576 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M)  : Prop := (t0 (a0) (t3 (t13 (M := M) (a1) (a3)) (t13 (M := M) (a2) (a4))))
noncomputable def g578 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M)  : Prop := (t0 (a0) (t3 (t13 (M := M) (a1) (a3)) (t13 (M := M) (a2) (a3))))
noncomputable def g579 (a0 : M) (a1 : M) (a2 : M)  : Prop := (t0 (t10 (M := M) (a0) (a1)) (t3 (t13 (M := M) (a0) (a2)) (t13 (M := M) (a1) (a2))))
noncomputable def g582 (a0 : M) (a1 : M)  : Prop := (t0 (t13 (M := M) (a0) (a1)) (t13 (M := M) (a1) (a0)))
noncomputable def g583 (a1 : M) (a2 : M → Prop) (z0 : M) : Prop := (t0 (t10 (M := M) z0 (a1)) (t3 (a2 z0) (t14 (M := M) (a1) (fun x2_1 : M => (a2 x2_1)))))
noncomputable def g585 (a1 : M) (a2 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (t14 (M := M) (a1) (fun x1_1 : M => (a2 x1_1)))))
noncomputable def g586 (a2 : M → M) (a3 : M → M → Prop) (z0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a3 x0_0 z0)))
noncomputable def g587 (a2 : M → M) (a3 : M → M → Prop) (z0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (t14 (M := M) (a2 z0) (fun x1_1 : M => (a3 x0_0 x1_1)))))
noncomputable def g588 (a1 : M → M) (a2 : M → M) (a3 : M → Prop) (z0 : M) : Prop := (t0 (t10 (M := M) (a1 z0) (a2 z0)) (t3 (t14 (M := M) (a1 z0) (fun x2_1 : M => (a3 x2_1))) (t14 (M := M) (a2 z0) (fun x2_1 : M => (a3 x2_1)))))
noncomputable def g589 (a1 : M → Prop) (a2 : M → M) (a3 : M → M) (a4 : M → Prop) (z0 : M) : Prop := (t0 (a1 z0) (t10 (M := M) (a2 z0) (a3 z0)))
noncomputable def g590 (a1 : M → Prop) (a2 : M → M) (a3 : M → M) (a4 : M → Prop) (z0 : M) : Prop := (t0 (a1 z0) (t3 (t14 (M := M) (a2 z0) (fun x2_1 : M => (a4 x2_1))) (t14 (M := M) (a3 z0) (fun x2_1 : M => (a4 x2_1)))))
noncomputable def g591 (a0 : Prop) (a2 : M → M) (a3 : M → M) (a4 : M → Prop) (a5 : M → Prop) (z0 : M) : Prop := (t0 (a0) (t10 (M := M) (a2 z0) (a3 z0)))
noncomputable def g592 (a0 : Prop) (a2 : M → M) (a3 : M → M) (a4 : M → Prop) (a5 : M → Prop) (z0 : M) : Prop := (t0 (a0) (t3 (a4 z0) (a5 z0)))
noncomputable def g593 (a0 : Prop) (a2 : M → M) (a3 : M → M) (a4 : M → Prop) (a5 : M → Prop) (z0 : M) : Prop := (t0 (a0) (t3 (t14 (M := M) (a2 z0) (fun x2_1 : M => (a4 x2_1))) (t14 (M := M) (a3 z0) (fun x2_1 : M => (a5 x2_1)))))
noncomputable def g594 (a0 : Prop) (a2 : M → M) (a3 : M → Prop) (a4 : M → Prop) (z0 : M) : Prop := (t0 (a0) (t3 (a3 z0) (a4 z0)))
noncomputable def g595 (a0 : Prop) (a2 : M → M) (a3 : M → Prop) (a4 : M → Prop) (z0 : M) : Prop := (t0 (a0) (t3 (t14 (M := M) (a2 z0) (fun x2_1 : M => (a3 x2_1))) (t14 (M := M) (a2 z0) (fun x2_1 : M => (a4 x2_1)))))
noncomputable def g598 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (t0 (t10 (M := M) x1_0 (a1)) (t3 (a2 x1_0) (a3 x1_0))))) (t3 (t14 (M := M) (a1) (fun x2_1 : M => (a2 x2_1))) (a3 z0)))
noncomputable def g599 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (z0 : M) : Prop := (t3 (t14 (M := M) (a1) (fun x1_1 : M => (a2 x1_1))) (a3 z0))
noncomputable def g600 (a1 : M) (a2 : M → Prop) (a3 : Prop)  : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (t0 (t10 (M := M) x1_0 (a1)) (t3 (a2 x1_0) (a3))))) (t3 (t14 (M := M) (a1) (fun x2_1 : M => (a2 x2_1))) (a3)))
noncomputable def g601 (a1 : M) (a2 : M → Prop) (a3 : Prop)  : Prop := (t3 (t14 (M := M) (a1) (fun x1_1 : M => (a2 x1_1))) (a3))
noncomputable def g602 (a0 : Prop) (a2 : M) (a3 : M → Prop) (a4 : Prop) (z0 : M) : Prop := (t0 (t2 (a0) (t10 (M := M) z0 (a2))) (t3 (a3 z0) (a4)))
noncomputable def g603 (a0 : Prop) (a2 : M) (a3 : M → Prop) (a4 : Prop)  : Prop := (t0 (a0) (t3 (t14 (M := M) (a2) (fun x2_1 : M => (a3 x2_1))) (a4)))
noncomputable def g604 (a1 : M) (a2 : M → Prop)  : Prop := (t3 (t14 (M := M) (a1) (fun x1_1 : M => (a2 x1_1))) (t8 (M := M) (fun x1_0 : M => (t0 (t10 (M := M) x1_0 (a1)) (a2 x1_0)))))
noncomputable def g605 (a1 : M) (a2 : M → Prop)  : Prop := (t3 (t14 (M := M) (a1) (fun x1_1 : M => (a2 x1_1))) (t9 (M := M) (fun x1_0 : M => (t2 (t10 (M := M) x1_0 (a1)) (a2 x1_0)))))
noncomputable def g606 (a2 : M → M) (a3 : M → Prop) (z0 : M) : Prop := (t3 (t14 (M := M) (a2 z0) (fun x1_1 : M => (t14 (M := M) x1_1 (fun x2_1 : M => (a3 x2_1))))) (t14 (M := M) (a2 z0) (fun x1_1 : M => (a3 x1_1))))
noncomputable def g607 (a1 : M → Prop) (z0 : M) : Prop := (t3 (t14 (M := M) z0 (fun x1_1 : M => (a1 x1_1))) (a1 z0))
noncomputable def g620 (a2 : M) (a3 : M → M → Prop) (a4 : M → M → Prop) (z0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a3 z0 x0_0)))
noncomputable def g621 (a2 : M) (a3 : M → M → Prop) (a4 : M → M → Prop) (z0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a4 x0_0 z0)))
noncomputable def g622 (a2 : M) (a3 : M → M → Prop) (a4 : M → M → Prop) (z0 : M) (z1 : M) : Prop := (t0 (t10 (M := M) z0 z1) (t3 (a3 z0 z1) (a4 z0 z1)))
noncomputable def g623 (a2 : M) (a3 : M → M → Prop) (a4 : M → M → Prop) (z0 : M) (z1 : M) : Prop := (t3 (t14 (M := M) (a2) (fun x1_1 : M => (a3 x1_1 z1))) (t14 (M := M) (a2) (fun x1_1 : M => (a4 z0 x1_1))))
noncomputable def g626 (a1 : M) (a2 : M → Prop) (a3 : Prop)  : Prop := (t3 (t8 (M := M) (fun x1_0 : M => (t0 (t10 (M := M) x1_0 (a1)) (a2 x1_0)))) (a3))
noncomputable def g628 (a1 : M) (a2 : M → Prop) (a3 : Prop)  : Prop := (t3 (t9 (M := M) (fun x1_0 : M => (t2 (t10 (M := M) x1_0 (a1)) (a2 x1_0)))) (a3))
noncomputable def g632 (a2 : M → Prop)  : Prop := (t3 (t8 (M := M) (fun x1_0 : M => (a2 x1_0))) (t8 (M := M) (fun x1_0 : M => (t14 (M := M) x1_0 (fun x2_1 : M => (a2 x2_1))))))
noncomputable def g633 (a2 : M → Prop)  : Prop := (t3 (t9 (M := M) (fun x1_0 : M => (a2 x1_0))) (t9 (M := M) (fun x1_0 : M => (t14 (M := M) x1_0 (fun x2_1 : M => (a2 x2_1))))))
noncomputable def g634 (a2 : Prop) (a3 : M → Prop) (a4 : M → Prop) (z0 : M) (z1 : M) : Prop := (t0 (t2 (a2) (t10 (M := M) z0 z1)) (t3 (a3 z0) (a4 z1)))
noncomputable def g635 (a2 : Prop) (a3 : M → Prop) (a4 : M → Prop)  : Prop := (t0 (a2) (t3 (t8 (M := M) (fun x2_0 : M => (a3 x2_0))) (t8 (M := M) (fun x2_0 : M => (a4 x2_0)))))
noncomputable def g636 (a2 : Prop) (a3 : M → Prop) (a4 : M → Prop)  : Prop := (t0 (a2) (t3 (t9 (M := M) (fun x2_0 : M => (a3 x2_0))) (t9 (M := M) (fun x2_0 : M => (a4 x2_0)))))
noncomputable def g640 (a0 : (M → Prop))  : Prop := (t17 (M := M) (a0) (a0))
noncomputable def g641 (a0 : (M → Prop)) (a1 : (M → Prop))  : Prop := (t0 (t17 (M := M) (a0) (a1)) (t17 (M := M) (a1) (a0)))
noncomputable def g642 (a0 : (M → Prop)) (a1 : (M → Prop))  : Prop := (t3 (t17 (M := M) (a0) (a1)) (t17 (M := M) (a1) (a0)))
noncomputable def g643 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : Prop := (t0 (t17 (M := M) (a0) (a1)) (t0 (t17 (M := M) (a1) (a2)) (t17 (M := M) (a0) (a2))))
noncomputable def g645 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : Prop := (t0 (t17 (M := M) (a1) (a0)) (t0 (t17 (M := M) (a1) (a2)) (t17 (M := M) (a0) (a2))))
noncomputable def g646 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : Prop := (t0 (t17 (M := M) (a0) (a1)) (t0 (t17 (M := M) (a2) (a1)) (t17 (M := M) (a0) (a2))))
noncomputable def g647 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop)  : Prop := (t0 (a3) (t17 (M := M) (a1) (a0)))
noncomputable def g648 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop)  : Prop := (t0 (a3) (t17 (M := M) (a1) (a2)))
noncomputable def g649 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop)  : Prop := (t0 (a3) (t17 (M := M) (a0) (a2)))
noncomputable def g650 (a0 : Prop) (a1 : (M → Prop))  : Prop := (t0 (a0) (t17 (M := M) (a1) (a1)))
noncomputable def g651 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : Prop)  : Prop := (t0 (a2) (t17 (M := M) (a0) (a1)))
noncomputable def g652 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : Prop)  : Prop := (t0 (a2) (t17 (M := M) (a1) (a0)))
noncomputable def g653 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop)  : Prop := (t0 (a3) (t17 (M := M) (a0) (a1)))
noncomputable def g654 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop)  : Prop := (t0 (a3) (t17 (M := M) (a2) (a1)))
noncomputable def g655 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop)  : Prop := (t17 (M := M) (a0) (a1))
noncomputable def g657 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop)  : Prop := (t17 (M := M) (a1) (a2))
noncomputable def g658 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop)  : Prop := (t17 (M := M) (a2) (a1))
noncomputable def g661 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : Prop)  : Prop := (t0 (a4) (t17 (M := M) (a0) (a1)))
noncomputable def g662 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : Prop)  : Prop := (t0 (a4) (t17 (M := M) (a2) (a3)))
noncomputable def g663 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : Prop)  : Prop := (t17 (M := M) (a2) (a0))
noncomputable def g664 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : Prop)  : Prop := (t17 (M := M) (a3) (a1))
noncomputable def g665 (a0 : (M → Prop)) (a1 : M) (a2 : M)  : Prop := (t0 (t10 (M := M) (a1) (a2)) (t3 (t16 (M := M) (a1) (a0)) (t16 (M := M) (a2) (a0))))
noncomputable def g666 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : M)  : Prop := (t0 (t17 (M := M) (a0) (a1)) (t3 (t16 (M := M) (a2) (a0)) (t16 (M := M) (a2) (a1))))
noncomputable def g667 (a0 : Prop) (a1 : M) (a2 : M) (a3 : (M → Prop))  : Prop := (t0 (a0) (t10 (M := M) (a1) (a2)))
noncomputable def g668 (a0 : Prop) (a1 : M) (a2 : M) (a3 : (M → Prop))  : Prop := (t0 (a0) (t3 (t16 (M := M) (a1) (a3)) (t16 (M := M) (a2) (a3))))
noncomputable def g669 (a0 : Prop) (a1 : M) (a2 : (M → Prop)) (a3 : (M → Prop))  : Prop := (t0 (a0) (t17 (M := M) (a2) (a3)))
noncomputable def g670 (a0 : Prop) (a1 : M) (a2 : (M → Prop)) (a3 : (M → Prop))  : Prop := (t0 (a0) (t3 (t16 (M := M) (a1) (a2)) (t16 (M := M) (a1) (a3))))
noncomputable def g671 (a0 : Prop) (a1 : M) (a2 : M) (a3 : (M → Prop)) (a4 : (M → Prop))  : Prop := (t0 (a0) (t10 (M := M) (a1) (a2)))
noncomputable def g672 (a0 : Prop) (a1 : M) (a2 : M) (a3 : (M → Prop)) (a4 : (M → Prop))  : Prop := (t0 (a0) (t17 (M := M) (a3) (a4)))
noncomputable def g673 (a0 : Prop) (a1 : M) (a2 : M) (a3 : (M → Prop)) (a4 : (M → Prop))  : Prop := (t0 (a0) (t3 (t16 (M := M) (a1) (a3)) (t16 (M := M) (a2) (a4))))
noncomputable def g674 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : (M → Prop))  : Prop := (t0 (a0) (t17 (M := M) (a1) (a2)))
noncomputable def g675 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : (M → Prop))  : Prop := (t0 (a0) (t17 (M := M) (a3) (a4)))
noncomputable def g676 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : (M → Prop))  : Prop := (t0 (a0) (t3 (t17 (M := M) (a1) (a3)) (t17 (M := M) (a2) (a4))))
noncomputable def g678 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop))  : Prop := (t0 (a0) (t17 (M := M) (a1) (a2)))
noncomputable def g679 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop))  : Prop := (t0 (a0) (t3 (t17 (M := M) (a1) (a3)) (t17 (M := M) (a2) (a3))))
noncomputable def g681 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop))  : Prop := (t0 (a0) (t17 (M := M) (a2) (a3)))
noncomputable def g682 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop))  : Prop := (t0 (a0) (t3 (t17 (M := M) (a1) (a2)) (t17 (M := M) (a1) (a3))))
noncomputable def g683 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : Prop := (t0 (t17 (M := M) (a1) (a2)) (t3 (t17 (M := M) (a0) (a1)) (t17 (M := M) (a0) (a2))))
noncomputable def g684 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (t3 (a1 x1_0) (a2 x1_0)))) (t17 (M := M) (t15 (M := M) (fun x2_0 : M => (a1 x2_0))) (t15 (M := M) (fun x2_0 : M => (a2 x2_0)))))
noncomputable def g685 (a0 : Prop) (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t0 (a0) (t17 (M := M) (t15 (M := M) (fun x2_0 : M => (a2 x2_0))) (t15 (M := M) (fun x2_0 : M => (a3 x2_0)))))
noncomputable def g686 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t17 (M := M) (t15 (M := M) (fun x1_0 : M => (a1 x1_0))) (t15 (M := M) (fun x1_0 : M => (a2 x1_0))))
noncomputable def g687 (a0 : (M → Prop)) (a1 : (M → Prop)) (z0 : M) : Prop := (t3 (t16 (M := M) z0 (a0)) (t16 (M := M) z0 (a1)))
noncomputable def g688 (a0 : (M → Prop)) (a1 : (M → Prop))  : Prop := (t17 (M := M) (a0) (a1))
noncomputable def g689 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : Prop) (z0 : M) : Prop := (t0 (a2) (t3 (t16 (M := M) z0 (a0)) (t16 (M := M) z0 (a1))))
noncomputable def g690 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : Prop)  : Prop := (t0 (a2) (t17 (M := M) (a0) (a1)))
noncomputable def g691 (a2 : M → M → Prop) (a3 : M → M → Prop) (z0 : M) (z1 : M) : Prop := (t17 (M := M) (t15 (M := M) (fun x1_0 : M => (a2 x1_0 z1))) (t15 (M := M) (fun x1_0 : M => (a3 z0 x1_0))))
noncomputable def g692 (a2 : M → Prop) (a3 : M → Prop)  : Prop := (t17 (M := M) (t15 (M := M) (fun x1_0 : M => (a2 x1_0))) (t15 (M := M) (fun x1_0 : M => (a3 x1_0))))
noncomputable def g695 (a1 : M → M) (a2 : M → Prop) (z0 : M) : Prop := (t3 (t16 (M := M) (a1 z0) (t15 (M := M) (fun x2_0 : M => (a2 x2_0)))) (t14 (M := M) (a1 z0) (fun x1_1 : M => (a2 x1_1))))
noncomputable def g696 (a1 : M) (a2 : M → Prop) (a3 : Prop)  : Prop := (t3 (t16 (M := M) (a1) (t15 (M := M) (fun x2_0 : M => (a2 x2_0)))) (a3))
noncomputable def g697 (a0 : Prop) (a2 : M) (a3 : M → Prop) (a4 : Prop)  : Prop := (t0 (a0) (t3 (t16 (M := M) (a2) (t15 (M := M) (fun x3_0 : M => (a3 x3_0)))) (a4)))
noncomputable def g704 (a1 : M → Prop) (z0 : M) : Prop := (t3 (t16 (M := M) z0 (t15 (M := M) (fun x2_0 : M => (a1 x2_0)))) (a1 z0))
noncomputable def g706 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : (M → Prop))  : Prop := (t0 (a0) (t3 (t18 (M := M) (a1) (a3)) (t18 (M := M) (a2) (a4))))
noncomputable def g708 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop))  : Prop := (t0 (a0) (t3 (t18 (M := M) (a1) (a3)) (t18 (M := M) (a2) (a3))))
noncomputable def g709 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : Prop := (t0 (t17 (M := M) (a0) (a1)) (t3 (t18 (M := M) (a0) (a2)) (t18 (M := M) (a1) (a2))))
noncomputable def g710 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop))  : Prop := (t0 (a0) (t3 (t18 (M := M) (a1) (a2)) (t18 (M := M) (a1) (a3))))
noncomputable def g711 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : Prop := (t0 (t17 (M := M) (a1) (a2)) (t3 (t18 (M := M) (a0) (a1)) (t18 (M := M) (a0) (a2))))
noncomputable def g713 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : M)  : Prop := (t0 (t18 (M := M) (a0) (a1)) (t0 (t16 (M := M) (a2) (a0)) (t16 (M := M) (a2) (a1))))
noncomputable def g714 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : Prop) (a3 : M)  : Prop := (t0 (a2) (t18 (M := M) (a0) (a1)))
noncomputable def g715 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : Prop) (a3 : M)  : Prop := (t0 (a2) (t16 (M := M) (a3) (a0)))
noncomputable def g716 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : Prop) (a3 : M)  : Prop := (t0 (a2) (t16 (M := M) (a3) (a1)))
noncomputable def g717 (a0 : (M → Prop))  : Prop := (t18 (M := M) (a0) (a0))
noncomputable def g718 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : Prop := (t0 (t18 (M := M) (a0) (a1)) (t0 (t18 (M := M) (a1) (a2)) (t18 (M := M) (a0) (a2))))
noncomputable def g719 (a0 : (M → Prop)) (a1 : (M → Prop))  : Prop := (t0 (t17 (M := M) (a0) (a1)) (t18 (M := M) (a0) (a1)))
noncomputable def g720 (a0 : (M → Prop)) (a1 : (M → Prop))  : Prop := (t0 (t17 (M := M) (a0) (a1)) (t18 (M := M) (a1) (a0)))
noncomputable def g721 (a0 : (M → Prop)) (a1 : (M → Prop))  : Prop := (t0 (t18 (M := M) (a0) (a1)) (t0 (t18 (M := M) (a1) (a0)) (t17 (M := M) (a0) (a1))))
noncomputable def g725 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : (M → Prop))  : Prop := (t0 (a0) (t17 (M := M) (t19 (M := M) (a1) (a3)) (t19 (M := M) (a2) (a4))))
noncomputable def g727 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop))  : Prop := (t0 (a0) (t17 (M := M) (t19 (M := M) (a1) (a3)) (t19 (M := M) (a2) (a3))))
noncomputable def g728 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : Prop := (t0 (t17 (M := M) (a0) (a1)) (t17 (M := M) (t19 (M := M) (a0) (a2)) (t19 (M := M) (a1) (a2))))
noncomputable def g731 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : M)  : Prop := (t3 (t16 (M := M) (a2) (t19 (M := M) (a0) (a1))) (t2 (t16 (M := M) (a2) (a0)) (t16 (M := M) (a2) (a1))))
noncomputable def g734 (a0 : (M → Prop)) (a1 : (M → Prop))  : Prop := (t18 (M := M) (t19 (M := M) (a0) (a1)) (a0))
noncomputable def g741 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : (M → Prop))  : Prop := (t0 (a0) (t17 (M := M) (t20 (M := M) (a1) (a3)) (t20 (M := M) (a2) (a4))))
noncomputable def g743 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop))  : Prop := (t0 (a0) (t17 (M := M) (t20 (M := M) (a1) (a3)) (t20 (M := M) (a2) (a3))))
noncomputable def g744 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : Prop := (t0 (t17 (M := M) (a0) (a1)) (t17 (M := M) (t20 (M := M) (a0) (a2)) (t20 (M := M) (a1) (a2))))
noncomputable def g747 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : M)  : Prop := (t3 (t16 (M := M) (a2) (t20 (M := M) (a0) (a1))) (t4 (t16 (M := M) (a2) (a0)) (t16 (M := M) (a2) (a1))))
noncomputable def g773 (a0 : M)  : Prop := (t16 (M := M) (a0) (t22 (M := M)))
noncomputable def g774 (a0 : (M → Prop))  : Prop := (t17 (M := M) (t19 (M := M) (t22 (M := M)) (a0)) (a0))
noncomputable def g785 (a0 : (M → Prop))  : Prop := (t23 (M := M) (fun x0_0 : M => (a0)))
noncomputable def g786 (a0 : M)  : Prop := (t24 (M := M) (fun x0_0 : M => (a0)))
noncomputable def g787 (a2 : M → (M → Prop)) (z0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (t16 (M := M) z0 (a2 x0_0))))
noncomputable def g788 (a2 : M → (M → Prop))  : Prop := (t23 (M := M) (fun x0_0 : M => (a2 x0_0)))
noncomputable def g789 (a2 : M → M) (z0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (t10 (M := M) z0 (a2 x0_0))))
noncomputable def g790 (a2 : M → M)  : Prop := (t24 (M := M) (fun x0_0 : M => (a2 x0_0)))
noncomputable def g791 (a1 : M) (a2 : M → (M → Prop))  : Prop := (t23 (M := M) (fun x0_0 : M => (a2 x0_0)))
noncomputable def g792 (a1 : M) (a2 : M → (M → Prop))  : Prop := (t11 (M := M) (fun x0_0 : M => (t16 (M := M) (a1) (a2 x0_0))))
noncomputable def g794 (a1 : M → (M → Prop)) (a2 : M → (M → Prop))  : Prop := (t23 (M := M) (fun x0_0 : M => (a2 x0_0)))
noncomputable def g795 (a1 : M → (M → Prop)) (a2 : M → (M → Prop))  : Prop := (t23 (M := M) (fun x0_0 : M => (a1 x0_0)))
noncomputable def g796 (a1 : M → M) (a2 : M → M)  : Prop := (t24 (M := M) (fun x0_0 : M => (a1 x0_0)))
noncomputable def g797 (a1 : M → M) (a2 : M → M)  : Prop := (t24 (M := M) (fun x0_0 : M => (a2 x0_0)))
noncomputable def g798 (a1 : M → M) (a2 : M → M)  : Prop := (t11 (M := M) (fun x0_0 : M => (t10 (M := M) (a1 x0_0) (a2 x0_0))))
noncomputable def g799 (a0 : M) (a2 : M → M)  : Prop := (t24 (M := M) (fun x0_0 : M => (a2 x0_0)))
noncomputable def g800 (a0 : M) (a2 : M → M)  : Prop := (t11 (M := M) (fun x0_0 : M => (t10 (M := M) (a0) (a2 x0_0))))
noncomputable def g801 (a1 : M → M) (a2 : M → Prop)  : Prop := (t24 (M := M) (fun x0_0 : M => (a1 x0_0)))
noncomputable def g802 (a1 : M → M) (a2 : M → Prop)  : Prop := (t11 (M := M) (fun x0_0 : M => (t14 (M := M) (a1 x0_0) (fun x1_1 : M => (a2 x1_1)))))
noncomputable def g803 (a2 : M → M → M) (a3 : M → M → Prop) (z0 : M) : Prop := (t24 (M := M) (fun x0_0 : M => (a2 x0_0 z0)))
noncomputable def g804 (a2 : M → M → M) (a3 : M → M → Prop) (z0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a3 x0_0 z0)))
noncomputable def g805 (a2 : M → M → M) (a3 : M → M → Prop) (z0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (t14 (M := M) (a2 x0_0 z0) (fun x1_1 : M => (a3 x0_0 x1_1)))))
noncomputable def g806 (a1 : M → M) (a2 : M → (M → Prop))  : Prop := (t24 (M := M) (fun x0_0 : M => (a1 x0_0)))
noncomputable def g807 (a1 : M → M) (a2 : M → (M → Prop))  : Prop := (t23 (M := M) (fun x0_0 : M => (a2 x0_0)))
noncomputable def g808 (a1 : M → M) (a2 : M → (M → Prop))  : Prop := (t11 (M := M) (fun x0_0 : M => (t16 (M := M) (a1 x0_0) (a2 x0_0))))
noncomputable def g809 (a1 : M → Prop)  : Prop := (t23 (M := M) (fun x0_0 : M => (t15 (M := M) (fun x1_0 : M => (a1 x1_0)))))
noncomputable def g810 (a2 : M → M → Prop)  : Prop := (t23 (M := M) (fun x0_0 : M => (t15 (M := M) (fun x1_0 : M => (a2 x0_0 x1_0)))))
noncomputable def g811 (a1 : M → (M → Prop)) (a2 : M → (M → Prop))  : Prop := (t11 (M := M) (fun x0_0 : M => (t17 (M := M) (a1 x0_0) (a2 x0_0))))
noncomputable def g812 (a1 : M → M) (a2 : M → M) (z0 : M) : Prop := (t10 (M := M) (a1 z0) (a2 z0))
noncomputable def g813 (a1 : M → (M → Prop)) (a2 : M → (M → Prop))  : Prop := (t23 (M := M) (fun x0_0 : M => (t19 (M := M) (a1 x0_0) (a2 x0_0))))
noncomputable def g816 (a0 : (M → Prop)) (a1 : Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (a1) (t3 (t16 (M := M) z0 (a0)) (a3 z0)))
noncomputable def g817 (a0 : (M → Prop)) (a1 : Prop) (a3 : M → Prop)  : Prop := (t0 (a1) (t17 (M := M) (a0) (t15 (M := M) (fun x2_0 : M => (a3 x2_0)))))
noncomputable def g818 (a0 : (M → Prop)) (a2 : M → Prop) (z0 : M) : Prop := (t3 (t16 (M := M) z0 (a0)) (a2 z0))
noncomputable def g819 (a0 : (M → Prop)) (a2 : M → Prop)  : Prop := (t17 (M := M) (a0) (t15 (M := M) (fun x1_0 : M => (a2 x1_0))))
noncomputable def g820 (a0 : (M → Prop)) (a1 : Prop) (a3 : M → Prop) (z0 : M) : Prop := (t0 (a1) (t3 (a3 z0) (t16 (M := M) z0 (a0))))
noncomputable def g821 (a0 : (M → Prop)) (a1 : Prop) (a3 : M → Prop)  : Prop := (t0 (a1) (t17 (M := M) (t15 (M := M) (fun x2_0 : M => (a3 x2_0))) (a0)))
noncomputable def g824 (a1 : M → Prop) (a2 : M → Prop)  : Prop := (t3 (t8 (M := M) (fun x1_0 : M => (t0 (a1 x1_0) (a2 x1_0)))) (t18 (M := M) (t15 (M := M) (fun x2_0 : M => (a1 x2_0))) (t15 (M := M) (fun x2_0 : M => (a2 x2_0)))))
noncomputable def g829 (a0 : (M → Prop)) (a2 : M → Prop)  : Prop := (t3 (t8 (M := M) (fun x1_0 : M => (t0 (t16 (M := M) x1_0 (a0)) (a2 x1_0)))) (t18 (M := M) (a0) (t15 (M := M) (fun x2_0 : M => (a2 x2_0)))))
noncomputable def g835 (a1 : M → M) (a2 : M) (a3 : M → (M → Prop)) (z0 : M) : Prop := (t3 (t16 (M := M) (a2) (t25 (M := M) (a1 z0) (fun x2_1 : M => (a3 x2_1)))) (t14 (M := M) (a1 z0) (fun x1_1 : M => (t16 (M := M) (a2) (a3 x1_1)))))
noncomputable def g836 (a1 : M) (a2 : M → (M → Prop)) (z0 : M) : Prop := (t0 (t10 (M := M) z0 (a1)) (t17 (M := M) (a2 z0) (t25 (M := M) (a1) (fun x2_1 : M => (a2 x2_1)))))
noncomputable def g837 (a1 : M → M) (a2 : M → (M → Prop))  : Prop := (t23 (M := M) (fun x0_0 : M => (t25 (M := M) (a1 x0_0) (fun x1_1 : M => (a2 x1_1)))))
noncomputable def g838 (a1 : M) (a2 : M → (M → Prop))  : Prop := (t23 (M := M) (fun x0_0 : M => (t25 (M := M) (a1) (fun x1_1 : M => (a2 x1_1)))))
noncomputable def g839 (a2 : M → M) (a3 : M → M → (M → Prop))  : Prop := (t24 (M := M) (fun x0_0 : M => (a2 x0_0)))
noncomputable def g840 (a2 : M → M) (a3 : M → M → (M → Prop)) (z0 : M) : Prop := (t23 (M := M) (fun x0_0 : M => (a3 x0_0 z0)))
noncomputable def g841 (a2 : M → M) (a3 : M → M → (M → Prop))  : Prop := (t23 (M := M) (fun x0_0 : M => (t25 (M := M) (a2 x0_0) (fun x1_1 : M => (a3 x0_0 x1_1)))))
noncomputable def g842 (a2 : M) (a3 : M → M → (M → Prop)) (z0 : M) : Prop := (t23 (M := M) (fun x0_0 : M => (a3 x0_0 z0)))
noncomputable def g843 (a2 : M) (a3 : M → M → (M → Prop))  : Prop := (t23 (M := M) (fun x0_0 : M => (t25 (M := M) (a2) (fun x1_1 : M => (a3 x0_0 x1_1)))))
noncomputable def g844 (a0 : Prop) (a2 : M) (a3 : M) (a4 : M → (M → Prop))  : Prop := (t0 (a0) (t10 (M := M) (a2) (a3)))
noncomputable def g845 (a0 : Prop) (a2 : M) (a3 : M) (a4 : M → (M → Prop))  : Prop := (t0 (a0) (t17 (M := M) (t25 (M := M) (a2) (fun x2_1 : M => (a4 x2_1))) (t25 (M := M) (a3) (fun x2_1 : M => (a4 x2_1)))))
noncomputable def g846 (a0 : Prop) (a2 : M → M) (a3 : M → (M → Prop)) (a4 : M → (M → Prop)) (z0 : M) : Prop := (t0 (a0) (t17 (M := M) (a3 z0) (a4 z0)))
noncomputable def g847 (a0 : Prop) (a2 : M → M) (a3 : M → (M → Prop)) (a4 : M → (M → Prop)) (z0 : M) : Prop := (t0 (a0) (t17 (M := M) (t25 (M := M) (a2 z0) (fun x2_1 : M => (a3 x2_1))) (t25 (M := M) (a2 z0) (fun x2_1 : M => (a4 x2_1)))))
noncomputable def g851 (a1 : M) (a2 : M → (M → Prop)) (a3 : M → (M → Prop))  : Prop := (t23 (M := M) (fun x0_0 : M => (a3 x0_0)))
noncomputable def g852 (a1 : M) (a2 : M → (M → Prop)) (a3 : M → (M → Prop)) (z0 : M) : Prop := (t0 (t8 (M := M) (fun x1_0 : M => (t0 (t10 (M := M) x1_0 (a1)) (t17 (M := M) (a2 x1_0) (a3 x1_0))))) (t17 (M := M) (t25 (M := M) (a1) (fun x2_1 : M => (a2 x2_1))) (a3 z0)))
noncomputable def g854 (a1 : M) (a2 : M → (M → Prop)) (a3 : M → (M → Prop)) (z0 : M) : Prop := (t0 (t10 (M := M) z0 (a1)) (t17 (M := M) (a2 z0) (a3 z0)))
noncomputable def g855 (a1 : M) (a2 : M → (M → Prop)) (a3 : M → (M → Prop)) (z0 : M) : Prop := (t17 (M := M) (t25 (M := M) (a1) (fun x1_1 : M => (a2 x1_1))) (a3 z0))
noncomputable def g857 (a1 : M) (a2 : M → (M → Prop)) (a3 : (M → Prop)) (z0 : M) : Prop := (t0 (t10 (M := M) z0 (a1)) (t17 (M := M) (a2 z0) (a3)))
noncomputable def g858 (a1 : M) (a2 : M → (M → Prop)) (a3 : (M → Prop))  : Prop := (t17 (M := M) (t25 (M := M) (a1) (fun x1_1 : M => (a2 x1_1))) (a3))
noncomputable def g885   : Prop := (t13 (M := M) (t30 (M := M)) (t28 (M := M)))
noncomputable def g886   : Prop := (t13 (M := M) (t31 (M := M)) (t28 (M := M)))
noncomputable def g887 (a0 : M) (a1 : M)  : Prop := (t0 (t10 (M := M) (a0) (a1)) (t10 (M := M) (t29 (M := M) (a0)) (t29 (M := M) (a1))))
noncomputable def g888 (a0 : Prop) (a1 : M) (a2 : M)  : Prop := (t0 (a0) (t10 (M := M) (t29 (M := M) (a1)) (t29 (M := M) (a2))))
noncomputable def g889 (a2 : M → M) (a3 : M → Prop) (a4 : M → Prop) (a5 : M → Prop) (a6 : M → Prop) (a7 : M → Prop) (z0 : M) (z1 : M) : Prop := (t0 (t10 (M := M) z0 (a2 z1)) (t3 (a3 z0) (a5 z1)))
noncomputable def g890 (a2 : M → M) (a3 : M → Prop) (a4 : M → Prop) (a5 : M → Prop) (a6 : M → Prop) (a7 : M → Prop) (z0 : M) (z1 : M) : Prop := (t0 (t10 (M := M) z0 (t28 (M := M))) (t3 (a3 z0) (a4 z1)))
noncomputable def g891 (a2 : M → M) (a3 : M → Prop) (a4 : M → Prop) (a5 : M → Prop) (a6 : M → Prop) (a7 : M → Prop) (z0 : M) (z1 : M) : Prop := (t0 (t10 (M := M) z0 z1) (t3 (a3 z0) (a6 z1)))
noncomputable def g892 (a2 : M → M) (a3 : M → Prop) (a4 : M → Prop) (a5 : M → Prop) (a6 : M → Prop) (a7 : M → Prop) (z0 : M) (z1 : M) : Prop := (t0 (t10 (M := M) z0 (t29 (M := M) z1)) (t3 (a3 z0) (a7 z1)))
noncomputable def g893 (a2 : M → M) (a3 : M → Prop) (a4 : M → Prop) (a5 : M → Prop) (a6 : M → Prop) (a7 : M → Prop) (z0 : M) : Prop := (a4 z0)
noncomputable def g894 (a2 : M → M) (a3 : M → Prop) (a4 : M → Prop) (a5 : M → Prop) (a6 : M → Prop) (a7 : M → Prop) (z0 : M) : Prop := (t0 (a6 z0) (a7 z0))
noncomputable def g895 (a2 : M → M) (a3 : M → Prop) (a4 : M → Prop) (a5 : M → Prop) (a6 : M → Prop) (a7 : M → Prop) (z0 : M) : Prop := (a5 z0)
theorem b0 (a0 : Prop) (a1 : Prop)  : (g0 a0 a1 ) := ZF207.MM0ModelPeano.«ax_1» a0 a1 
theorem b1 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g1 a0 a1 a2 ) := ZF207.MM0ModelPeano.«ax_2» a0 a1 a2 
theorem b2 (a0 : Prop) (a1 : Prop)  : (g2 a0 a1 ) := ZF207.MM0ModelPeano.«ax_3» a0 a1 
theorem b3 (a0 : Prop) (a1 : Prop) (h0 : (g3 a0 a1 )) (h1 : (g4 a0 a1 )) : (g5 a0 a1 ) := ZF207.MM0ModelPeano.«ax_mp» a0 a1 h0 h1
theorem b317   : (g6  ) := ZF207.MM0ModelPeano.«itru»  
theorem b325 (a1 : M → Prop) (h0 : (∀ z0 : M, (g7 (M := M) a1 z0))) : (g8 (M := M) a1 ) := ZF207.MM0ModelPeano.«ax_gen» a1 h0
theorem b326 (a1 : M → Prop) (a2 : M → Prop)  : (g9 (M := M) a1 a2 ) := ZF207.MM0ModelPeano.«ax_4» a1 a2 
theorem b328 (a1 : Prop)  : (g10 (M := M) a1 ) := ZF207.MM0ModelPeano.«ax_5» a1 
theorem b330 (a0 : M)  : (g11 (M := M) a0 ) := ZF207.MM0ModelPeano.«ax_6» a0 
theorem b331 (a0 : M) (a1 : M) (a2 : M)  : (g12 (M := M) a0 a1 a2 ) := ZF207.MM0ModelPeano.«ax_7» a0 a1 a2 
theorem b333 (a1 : M → Prop)  : (g13 (M := M) a1 ) := ZF207.MM0ModelPeano.«ax_10» a1 
theorem b334 (a2 : M → M → Prop)  : (g14 (M := M) a2 ) := ZF207.MM0ModelPeano.«ax_11» a2 
theorem b336 (a1 : M) (a2 : M → Prop)  : (∀ z0 : M, (g15 (M := M) a1 a2 z0)) := fun z0 : M => ZF207.MM0ModelPeano.«ax_12» z0 a1 a2 
theorem b552 (a0 : M) (a2 : M → Prop)  : (g16 (M := M) a0 a2 ) := ZF207.MM0ModelPeano.«elab» a0 a2 
theorem b553 (a0 : M) (a1 : M) (a2 : (M → Prop))  : (g17 (M := M) a0 a1 a2 ) := ZF207.MM0ModelPeano.«ax_8» a0 a1 a2 
theorem b734 (a0 : M)  : (g18 (M := M) a0 ) := ZF207.MM0ModelPeano.«peano1» a0 
theorem b735 (a0 : M) (a1 : M)  : (g19 (M := M) a0 a1 ) := ZF207.MM0ModelPeano.«peano2» a0 a1 
theorem b736 (a1 : M → Prop) (e : Nat → M) (certificate : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => a1 (v 0)))  : (g20 (M := M) a1 ) := by
  intro hz hs
  apply certificate.induction
  · exact hz 0 rfl 0 rfl
  · intro x hx; exact hs x hx (x+1) rfl (x+1) rfl
theorem p4 (a0 : Prop) (a1 : Prop) (h0 : (g5 a0 a1 )) : (g3 a0 a1 ) := ZF207.MM0ReplayProp.mm_t4 a0 a1 h0
theorem p5 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g21 a0 a1 a2 )) : (g22 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t5 a0 a1 a2 h0
theorem p6 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g23 a0 a1 a2 )) (h1 : (g21 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t6 a0 a1 a2 h0 h1
theorem p7 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g25 a0 a1 a2 )) (h1 : (g21 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t7 a0 a1 a2 h0 h1
theorem p8 (a0 : Prop)  : (g26 a0 ) := ZF207.MM0ReplayProp.mm_t8 a0 
theorem p10 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g28 a0 a1 a2 )) (h1 : (g23 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t10 a0 a1 a2 h0 h1
theorem p11 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g23 a0 a1 a2 )) (h1 : (g28 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t11 a0 a1 a2 h0 h1
theorem p12 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g23 a0 a1 a2 )) : (g29 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t12 a0 a1 a2 h0
theorem p13 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g30 a0 a1 a2 a3 )) : (g31 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t13 a0 a1 a2 a3 h0
theorem p15 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g33 a0 a1 a2 a3 )) (h1 : (g34 a0 a1 a2 a3 )) (h2 : (g35 a0 a1 a2 a3 )) : (g36 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t15 a0 a1 a2 a3 h0 h1 h2
theorem p16 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g37 a0 a1 a2 a3 )) (h1 : (g38 a0 a1 a2 a3 )) : (g39 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t16 a0 a1 a2 a3 h0 h1
theorem p17 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g40 a0 a1 a2 a3 )) (h1 : (g38 a0 a1 a2 a3 )) : (g39 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t17 a0 a1 a2 a3 h0 h1
theorem p18 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g41 a0 a1 a2 a3 )) (h1 : (g37 a0 a1 a2 a3 )) : (g39 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t18 a0 a1 a2 a3 h0 h1
theorem p19 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g42 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t19 a0 a1 a2 
theorem p20 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g28 a0 a1 a2 )) : (g22 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t20 a0 a1 a2 h0
theorem p21 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g38 a0 a1 a2 a3 )) : (g31 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t21 a0 a1 a2 a3 h0
theorem p22 (a0 : Prop) (a1 : Prop)  : (g43 a0 a1 ) := ZF207.MM0ReplayProp.mm_t22 a0 a1 
theorem p23 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g21 a0 a1 a2 )) : (g44 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t23 a0 a1 a2 h0
theorem p24 (a0 : Prop) (a1 : Prop)  : (g45 a0 a1 ) := ZF207.MM0ReplayProp.mm_t24 a0 a1 
theorem p27 (a0 : Prop) (a1 : Prop)  : (g48 a0 a1 ) := ZF207.MM0ReplayProp.mm_t27 a0 a1 
theorem p29 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g23 a0 a1 a2 )) : (g50 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t29 a0 a1 a2 h0
theorem p30 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g37 a0 a1 a2 a3 )) : (g51 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t30 a0 a1 a2 a3 h0
theorem p33 (a0 : Prop) (a1 : Prop)  : (g56 a0 a1 ) := ZF207.MM0ReplayProp.mm_t33 a0 a1 
theorem p35 (a0 : Prop)  : (g58 a0 ) := ZF207.MM0ReplayProp.mm_t35 a0 
theorem p37 (a0 : Prop)  : (g60 a0 ) := ZF207.MM0ReplayProp.mm_t37 a0 
theorem p38 (a0 : Prop) (a1 : Prop)  : (g61 a0 a1 ) := ZF207.MM0ReplayProp.mm_t38 a0 a1 
theorem p39 (a0 : Prop)  : (g62 a0 ) := ZF207.MM0ReplayProp.mm_t39 a0 
theorem p40 (a0 : Prop) (a1 : Prop)  : (g63 a0 a1 ) := ZF207.MM0ReplayProp.mm_t40 a0 a1 
theorem p41 (a0 : Prop) (a1 : Prop)  : (g64 a0 a1 ) := ZF207.MM0ReplayProp.mm_t41 a0 a1 
theorem p42 (a0 : Prop) (a1 : Prop) (h0 : (g3 a0 a1 )) (h1 : (g65 a0 a1 )) : (g5 a0 a1 ) := ZF207.MM0ReplayProp.mm_t42 a0 a1 h0 h1
theorem p43 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g21 a0 a1 a2 )) (h1 : (g66 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t43 a0 a1 a2 h0 h1
theorem p44 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g66 a0 a1 a2 )) : (g67 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t44 a0 a1 a2 h0
theorem p46 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g21 a0 a1 a2 )) : (g70 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t46 a0 a1 a2 h0
theorem p47 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g32 a0 a1 a2 )) : (g29 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t47 a0 a1 a2 h0
theorem p48 (a0 : Prop) (a1 : Prop) (h0 : (g71 a0 a1 )) (h1 : (g72 a0 a1 )) : (g73 a0 a1 ) := ZF207.MM0ReplayProp.mm_t48 a0 a1 h0 h1
theorem p50 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g75 a0 a1 a2 )) (h1 : (g29 a0 a1 a2 )) : (g76 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t50 a0 a1 a2 h0 h1
theorem p53 (a0 : Prop) (a1 : Prop)  : (g78 a0 a1 ) := ZF207.MM0ReplayProp.mm_t53 a0 a1 
theorem p54 (a0 : Prop) (a1 : Prop)  : (g79 a0 a1 ) := ZF207.MM0ReplayProp.mm_t54 a0 a1 
theorem p57 (a0 : Prop) (a1 : Prop)  : (g81 a0 a1 ) := ZF207.MM0ReplayProp.mm_t57 a0 a1 
theorem p58 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g23 a0 a1 a2 )) (h1 : (g24 a0 a1 a2 )) : (g82 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t58 a0 a1 a2 h0 h1
theorem p59 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g82 a0 a1 a2 )) : (g23 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t59 a0 a1 a2 h0
theorem p60 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g82 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t60 a0 a1 a2 h0
theorem p62 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g24 a0 a1 a2 )) : (g83 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t62 a0 a1 a2 h0
theorem p63 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g28 a0 a1 a2 )) : (g83 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t63 a0 a1 a2 h0
theorem p64 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g84 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t64 a0 a1 a2 
theorem p65 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g85 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t65 a0 a1 a2 
theorem p66 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g86 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t66 a0 a1 a2 
theorem p67 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g87 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t67 a0 a1 a2 
theorem p68 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g36 a0 a1 a2 a3 )) : (g88 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t68 a0 a1 a2 a3 h0
theorem p69 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (h0 : (g89 a0 a1 a2 a3 a4 )) : (g90 a0 a1 a2 a3 a4 ) := ZF207.MM0ReplayProp.mm_t69 a0 a1 a2 a3 a4 h0
theorem p74 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : (g99 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t74 a0 a1 a2 a3 
theorem p75 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : (g100 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t75 a0 a1 a2 a3 
theorem p83 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g21 a0 a1 a2 )) : (g83 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t83 a0 a1 a2 h0
theorem p84 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g83 a0 a1 a2 )) : (g21 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t84 a0 a1 a2 h0
theorem p85 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g21 a0 a1 a2 )) : (g108 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t85 a0 a1 a2 h0
theorem p87 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g109 a0 a1 a2 a3 )) (h1 : (g110 a0 a1 a2 a3 )) : (g36 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t87 a0 a1 a2 a3 h0 h1
theorem p88 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g111 a0 a1 a2 a3 )) (h1 : (g34 a0 a1 a2 a3 )) (h2 : (g35 a0 a1 a2 a3 )) : (g36 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t88 a0 a1 a2 a3 h0 h1 h2
theorem p89 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (h0 : (g52 a0 a1 a2 a3 a4 )) (h1 : (g53 a0 a1 a2 a3 a4 )) : (g112 a0 a1 a2 a3 a4 ) := ZF207.MM0ReplayProp.mm_t89 a0 a1 a2 a3 a4 h0 h1
theorem p91 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g38 a0 a1 a2 a3 )) : (g114 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t91 a0 a1 a2 a3 h0
theorem p92 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g115 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t92 a0 a1 a2 
theorem p93 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g116 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t93 a0 a1 a2 
theorem p97 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g88 a0 a1 a2 a3 )) : (g120 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t97 a0 a1 a2 a3 h0
theorem p99 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g83 a0 a1 a2 )) (h1 : (g122 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t99 a0 a1 a2 h0 h1
theorem p102 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g75 a0 a1 a2 )) (h1 : (g125 a0 a1 a2 )) : (g76 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t102 a0 a1 a2 h0 h1
theorem p103 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g77 a0 a1 a2 )) (h1 : (g125 a0 a1 a2 )) : (g76 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t103 a0 a1 a2 h0 h1
theorem p104 (a0 : Prop) (a1 : Prop)  : (g126 a0 a1 ) := ZF207.MM0ReplayProp.mm_t104 a0 a1 
theorem p105 (a0 : Prop) (a1 : Prop) (h0 : (g127 a0 a1 )) : (g3 a0 a1 ) := ZF207.MM0ReplayProp.mm_t105 a0 a1 h0
theorem p106 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g128 a0 a1 a2 )) : (g21 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t106 a0 a1 a2 h0
theorem p108 (a0 : Prop) (a1 : Prop)  : (g129 a0 a1 ) := ZF207.MM0ReplayProp.mm_t108 a0 a1 
theorem p109 (a0 : Prop) (a1 : Prop) (h0 : (g127 a0 a1 )) : (g71 a0 a1 ) := ZF207.MM0ReplayProp.mm_t109 a0 a1 h0
theorem p110 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g128 a0 a1 a2 )) : (g29 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t110 a0 a1 a2 h0
theorem p112 (a0 : Prop) (a1 : Prop) (h0 : (g3 a0 a1 )) (h1 : (g71 a0 a1 )) : (g127 a0 a1 ) := ZF207.MM0ReplayProp.mm_t112 a0 a1 h0 h1
theorem p113 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g21 a0 a1 a2 )) (h1 : (g29 a0 a1 a2 )) : (g128 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t113 a0 a1 a2 h0 h1
theorem p114 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g83 a0 a1 a2 )) (h1 : (g125 a0 a1 a2 )) : (g128 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t114 a0 a1 a2 h0 h1
theorem p115 (a0 : Prop)  : (g130 a0 ) := ZF207.MM0ReplayProp.mm_t115 a0 
theorem p116 (a0 : Prop) (a1 : Prop)  : (g131 a0 a1 ) := ZF207.MM0ReplayProp.mm_t116 a0 a1 
theorem p117 (a0 : Prop) (a1 : Prop) (h0 : (g127 a0 a1 )) (h1 : (g4 a0 a1 )) : (g5 a0 a1 ) := ZF207.MM0ReplayProp.mm_t117 a0 a1 h0 h1
theorem p118 (a0 : Prop) (a1 : Prop) (h0 : (g132 a0 a1 )) (h1 : (g4 a0 a1 )) : (g5 a0 a1 ) := ZF207.MM0ReplayProp.mm_t118 a0 a1 h0 h1
theorem p119 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g128 a0 a1 a2 )) (h1 : (g23 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t119 a0 a1 a2 h0 h1
theorem p120 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g133 a0 a1 a2 )) (h1 : (g23 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t120 a0 a1 a2 h0 h1
theorem p121 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g25 a0 a1 a2 )) (h1 : (g128 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t121 a0 a1 a2 h0 h1
theorem p122 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g25 a0 a1 a2 )) (h1 : (g133 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t122 a0 a1 a2 h0 h1
theorem p123 (a0 : Prop) (a1 : Prop) (h0 : (g127 a0 a1 )) (h1 : (g72 a0 a1 )) : (g73 a0 a1 ) := ZF207.MM0ReplayProp.mm_t123 a0 a1 h0 h1
theorem p124 (a0 : Prop) (a1 : Prop) (h0 : (g132 a0 a1 )) (h1 : (g72 a0 a1 )) : (g73 a0 a1 ) := ZF207.MM0ReplayProp.mm_t124 a0 a1 h0 h1
theorem p126 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g133 a0 a1 a2 )) (h1 : (g75 a0 a1 a2 )) : (g76 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t126 a0 a1 a2 h0 h1
theorem p128 (a0 : Prop) (a1 : Prop)  : (g135 a0 a1 ) := ZF207.MM0ReplayProp.mm_t128 a0 a1 
theorem p130 (a0 : Prop) (a1 : Prop)  : (g137 a0 a1 ) := ZF207.MM0ReplayProp.mm_t130 a0 a1 
theorem p137 (a0 : Prop)  : (g144 a0 ) := ZF207.MM0ReplayProp.mm_t137 a0 
theorem p139 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g75 a0 a1 a2 )) (h1 : (g76 a0 a1 a2 )) : (g128 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t139 a0 a1 a2 h0 h1
theorem p140 (a0 : Prop) (a1 : Prop)  : (g145 a0 a1 ) := ZF207.MM0ReplayProp.mm_t140 a0 a1 
theorem p141 (a0 : Prop) (a1 : Prop)  : (g146 a0 a1 ) := ZF207.MM0ReplayProp.mm_t141 a0 a1 
theorem p142 (a0 : Prop) (a1 : Prop)  : (g147 a0 a1 ) := ZF207.MM0ReplayProp.mm_t142 a0 a1 
theorem p144 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g128 a0 a1 a2 )) : (g133 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t144 a0 a1 a2 h0
theorem p145 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g149 a0 a1 a2 a3 )) (h1 : (g150 a0 a1 a2 a3 )) : (g151 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t145 a0 a1 a2 a3 h0 h1
theorem p147 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g153 a0 a1 a2 a3 )) (h1 : (g150 a0 a1 a2 a3 )) : (g151 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t147 a0 a1 a2 a3 h0 h1
theorem p148 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g149 a0 a1 a2 a3 )) (h1 : (g154 a0 a1 a2 a3 )) : (g151 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t148 a0 a1 a2 a3 h0 h1
theorem p149 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g155 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t149 a0 a1 a2 
theorem p151 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g157 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t151 a0 a1 a2 
theorem p152 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g158 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t152 a0 a1 a2 
theorem p153 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g159 a0 a1 a2 )) (h1 : (g23 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t153 a0 a1 a2 h0 h1
theorem p154 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g160 a0 a1 a2 )) (h1 : (g23 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t154 a0 a1 a2 h0 h1
theorem p155 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g161 a0 a1 a2 )) (h1 : (g28 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t155 a0 a1 a2 h0 h1
theorem p156 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g162 a0 a1 a2 )) (h1 : (g28 a0 a1 a2 )) : (g24 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t156 a0 a1 a2 h0 h1
theorem p157 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g163 a0 a1 a2 a3 )) (h1 : (g150 a0 a1 a2 a3 )) : (g151 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t157 a0 a1 a2 a3 h0 h1
theorem p158 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g164 a0 a1 a2 a3 )) (h1 : (g150 a0 a1 a2 a3 )) : (g151 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t158 a0 a1 a2 a3 h0 h1
theorem p159 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g165 a0 a1 a2 a3 )) (h1 : (g149 a0 a1 a2 a3 )) : (g151 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t159 a0 a1 a2 a3 h0 h1
theorem p160 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g166 a0 a1 a2 a3 )) (h1 : (g149 a0 a1 a2 a3 )) : (g151 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t160 a0 a1 a2 a3 h0 h1
theorem p161 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g163 a0 a1 a2 a3 )) (h1 : (g38 a0 a1 a2 a3 )) : (g39 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t161 a0 a1 a2 a3 h0 h1
theorem p162 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g164 a0 a1 a2 a3 )) (h1 : (g38 a0 a1 a2 a3 )) : (g39 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t162 a0 a1 a2 a3 h0 h1
theorem p163 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g165 a0 a1 a2 a3 )) (h1 : (g37 a0 a1 a2 a3 )) : (g39 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t163 a0 a1 a2 a3 h0 h1
theorem p164 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g166 a0 a1 a2 a3 )) (h1 : (g37 a0 a1 a2 a3 )) : (g39 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t164 a0 a1 a2 a3 h0 h1
theorem p165 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g167 a0 a1 a2 a3 )) (h1 : (g36 a0 a1 a2 a3 )) : (g168 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t165 a0 a1 a2 a3 h0 h1
theorem p172 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (h0 : (g173 a0 a1 a2 a3 a4 )) (h1 : (g174 a0 a1 a2 a3 a4 )) (h2 : (g171 a0 a1 a2 a3 a4 )) : (g172 a0 a1 a2 a3 a4 ) := ZF207.MM0ReplayProp.mm_t172 a0 a1 a2 a3 a4 h0 h1 h2
theorem p174 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g178 a0 a1 a2 a3 )) (h1 : (g179 a0 a1 a2 a3 )) (h2 : (g177 a0 a1 a2 a3 )) : (g165 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t174 a0 a1 a2 a3 h0 h1 h2
theorem p175 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g128 a0 a1 a2 )) : (g83 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t175 a0 a1 a2 h0
theorem p177 (a0 : Prop) (a1 : Prop)  : (g180 a0 a1 ) := ZF207.MM0ReplayProp.mm_t177 a0 a1 
theorem p180 (a0 : Prop) (a1 : Prop)  : (g183 a0 a1 ) := ZF207.MM0ReplayProp.mm_t180 a0 a1 
theorem p181 (a0 : Prop) (a1 : Prop)  : (g184 a0 a1 ) := ZF207.MM0ReplayProp.mm_t181 a0 a1 
theorem p182 (a0 : Prop) (a1 : Prop)  : (g185 a0 a1 ) := ZF207.MM0ReplayProp.mm_t182 a0 a1 
theorem p185 (a0 : Prop) (a1 : Prop)  : (g136 a0 a1 ) := ZF207.MM0ReplayProp.mm_t185 a0 a1 
theorem p187 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g128 a0 a1 a2 )) : (g189 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t187 a0 a1 a2 h0
theorem p188 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (h0 : (g171 a0 a1 a2 a3 a4 )) (h1 : (g172 a0 a1 a2 a3 a4 )) : (g190 a0 a1 a2 a3 a4 ) := ZF207.MM0ReplayProp.mm_t188 a0 a1 a2 a3 a4 h0 h1
theorem p191 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g149 a0 a1 a2 a3 )) : (g193 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t191 a0 a1 a2 a3 h0
theorem p192 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g150 a0 a1 a2 a3 )) : (g194 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t192 a0 a1 a2 a3 h0
theorem p193 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g161 a0 a1 a2 )) : (g195 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t193 a0 a1 a2 h0
theorem p194 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g159 a0 a1 a2 )) : (g196 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t194 a0 a1 a2 h0
theorem p195 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g177 a0 a1 a2 a3 )) (h1 : (g165 a0 a1 a2 a3 )) : (g197 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t195 a0 a1 a2 a3 h0 h1
theorem p196 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (h0 : (g171 a0 a1 a2 a3 a4 )) (h1 : (g172 a0 a1 a2 a3 a4 )) : (g198 a0 a1 a2 a3 a4 ) := ZF207.MM0ReplayProp.mm_t196 a0 a1 a2 a3 a4 h0 h1
theorem p200 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g149 a0 a1 a2 a3 )) : (g202 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t200 a0 a1 a2 a3 h0
theorem p201 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g150 a0 a1 a2 a3 )) : (g203 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t201 a0 a1 a2 a3 h0
theorem p202 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : (g204 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t202 a0 a1 a2 a3 
theorem p203 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g161 a0 a1 a2 )) : (g205 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t203 a0 a1 a2 h0
theorem p204 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g159 a0 a1 a2 )) : (g206 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t204 a0 a1 a2 h0
theorem p205 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g207 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t205 a0 a1 a2 
theorem p206 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g208 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t206 a0 a1 a2 
theorem p231 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g233 a0 a1 a2 a3 )) (h1 : (g234 a0 a1 a2 a3 )) (h2 : (g201 a0 a1 a2 a3 )) : (g150 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t231 a0 a1 a2 a3 h0 h1 h2
theorem p232 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g235 a0 a1 a2 )) (h1 : (g236 a0 a1 a2 )) (h2 : (g128 a0 a1 a2 )) : (g159 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t232 a0 a1 a2 h0 h1 h2
theorem p233 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (h0 : (g171 a0 a1 a2 a3 a4 )) (h1 : (g172 a0 a1 a2 a3 a4 )) : (g237 a0 a1 a2 a3 a4 ) := ZF207.MM0ReplayProp.mm_t233 a0 a1 a2 a3 a4 h0 h1
theorem p234 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g149 a0 a1 a2 a3 )) : (g238 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t234 a0 a1 a2 a3 h0
theorem p235 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g150 a0 a1 a2 a3 )) : (g239 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t235 a0 a1 a2 a3 h0
theorem p236 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : (g240 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t236 a0 a1 a2 a3 
theorem p238 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g242 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t238 a0 a1 a2 
theorem p239 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g243 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t239 a0 a1 a2 
theorem p243 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (h0 : (g171 a0 a1 a2 a3 a4 )) (h1 : (g172 a0 a1 a2 a3 a4 )) : (g246 a0 a1 a2 a3 a4 ) := ZF207.MM0ReplayProp.mm_t243 a0 a1 a2 a3 a4 h0 h1
theorem p244 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop)  : (g247 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t244 a0 a1 a2 a3 
theorem p245 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g149 a0 a1 a2 a3 )) : (g248 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t245 a0 a1 a2 a3 h0
theorem p246 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g249 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t246 a0 a1 a2 
theorem p247 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g150 a0 a1 a2 a3 )) : (g250 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t247 a0 a1 a2 a3 h0
theorem p249 (a0 : Prop) (a1 : Prop)  : (g252 a0 a1 ) := ZF207.MM0ReplayProp.mm_t249 a0 a1 
theorem p250 (a0 : Prop) (a1 : Prop)  : (g253 a0 a1 ) := ZF207.MM0ReplayProp.mm_t250 a0 a1 
theorem p252 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g39 a0 a1 a2 a3 )) (h1 : (g38 a0 a1 a2 a3 )) : (g255 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t252 a0 a1 a2 a3 h0 h1
theorem p253 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g256 a0 a1 a2 a3 )) (h1 : (g257 a0 a1 a2 a3 )) : (g255 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t253 a0 a1 a2 a3 h0 h1
theorem p254 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g23 a0 a1 a2 )) : (g258 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t254 a0 a1 a2 h0
theorem p255 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g24 a0 a1 a2 )) : (g258 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t255 a0 a1 a2 h0
theorem p256 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g259 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t256 a0 a1 a2 
theorem p262 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g161 a0 a1 a2 )) : (g265 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t262 a0 a1 a2 h0
theorem p263 (a0 : Prop) (a1 : Prop) (a2 : Prop) (h0 : (g159 a0 a1 a2 )) : (g266 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t263 a0 a1 a2 h0
theorem p265 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h0 : (g177 a0 a1 a2 a3 )) (h1 : (g165 a0 a1 a2 a3 )) : (g268 a0 a1 a2 a3 ) := ZF207.MM0ReplayProp.mm_t265 a0 a1 a2 a3 h0 h1
theorem p266 (a0 : Prop) (a1 : Prop)  : (g269 a0 a1 ) := ZF207.MM0ReplayProp.mm_t266 a0 a1 
theorem p267 (a0 : Prop) (a1 : Prop)  : (g270 a0 a1 ) := ZF207.MM0ReplayProp.mm_t267 a0 a1 
theorem p272 (a0 : Prop) (a1 : Prop)  : (g275 a0 a1 ) := ZF207.MM0ReplayProp.mm_t272 a0 a1 
theorem p274 (a0 : Prop) (a1 : Prop)  : (g277 a0 a1 ) := ZF207.MM0ReplayProp.mm_t274 a0 a1 
theorem p277 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g280 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t277 a0 a1 a2 
theorem p278 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g281 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t278 a0 a1 a2 
theorem p287 (a0 : Prop) (a1 : Prop)  : (g290 a0 a1 ) := ZF207.MM0ReplayProp.mm_t287 a0 a1 
theorem p290 (a0 : Prop) (a1 : Prop)  : (g293 a0 a1 ) := ZF207.MM0ReplayProp.mm_t290 a0 a1 
theorem p295 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (h0 : (g298 a0 a1 a2 a3 a4 a5 a6 )) (h1 : (g299 a0 a1 a2 a3 a4 a5 a6 )) (h2 : (g300 a0 a1 a2 a3 a4 a5 a6 )) : (g301 a0 a1 a2 a3 a4 a5 a6 ) := ZF207.MM0ReplayProp.mm_t295 a0 a1 a2 a3 a4 a5 a6 h0 h1 h2
theorem p303 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g310 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t303 a0 a1 a2 
theorem p304 (a0 : Prop) (a1 : Prop) (a2 : Prop)  : (g311 a0 a1 a2 ) := ZF207.MM0ReplayProp.mm_t304 a0 a1 a2 
theorem p318 (a0 : Prop) (h0 : (g327 a0 )) : (g328 a0 ) := ZF207.MM0ReplayProp.mm_t318 a0 h0
theorem p320   : (g330  ) := ZF207.MM0ReplayProp.mm_t320  
theorem p323 (a0 : Prop)  : (g333 a0 ) := ZF207.MM0ReplayProp.mm_t323 a0 
theorem p332 (a0 : M) (a1 : M) (a2 : M)  : (g335 (M := M) a0 a1 a2 ) := by
  have v0 : ((show Prop from (t0 ((show Prop from (t10 (M := M) (a1) (a0)))) ((show Prop from (t0 ((show Prop from (t10 (M := M) (a1) (a2)))) ((show Prop from (t10 (M := M) (a0) (a2)))))))))) := b331 (M := M) (a1) (a0) (a2)
  exact v0
-- Actual MMB 337 alimi
theorem p337 (a1 : M → Prop) (a2 : M → Prop) (h0 : (∀ z0 : M, (g336 (M := M) a1 a2 z0))) : (g337 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t0 (a1 u0) (a2 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4  : Prop := (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (a1 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (a2 x0_0))))))
  have v0 : ((show Prop from (t0 (e1) (e4)))) := b326 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (a2 w0))
  have v1 : (e1) := b325 (M := M) (fun w0 : M => (e0 w0)) ((fun w0 : M => h0 w0))
  have v2 : (e4) := b3 (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 338 iald
theorem p338 (a1 : Prop) (a2 : M → Prop) (h0 : (∀ z0 : M, (g338 (M := M) a1 a2 z0))) : (g339 (M := M) a1 a2 ) := by
  let e0  : Prop := (t8 (M := M) (fun x0_0 : M => (a1)))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (a2 x0_0)))
  have v0 : ((show Prop from (t0 (e0) (e1)))) := p337 (M := M) (fun w0 : M => (a1)) (fun w0 : M => (a2 w0)) ((fun w0 : M => h0 w0))
  have v1 : ((show Prop from (t0 (a1) (e0)))) := b328 (M := M) (a1)
  have v2 : ((show Prop from (t0 (a1) (e1)))) := p10 (a1) (e0) (e1) (v0) (v1)
  exact v2
-- Actual MMB 339 eex
theorem p339 (a1 : M → Prop) (a2 : Prop) (h0 : (∀ z0 : M, (g340 (M := M) a1 a2 z0))) : (g341 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t1 (a1 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e2  : Prop := (t1 (a2))
  let e3  : Prop := (t0 (e2) (e1))
  let e8  : Prop := (t0 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a1 x0_0))))) (a2))
  let e9  : Prop := (t0 (e3) (e8))
  let e10 (u0 : M) : Prop := (t0 (a1 u0) (a2))
  let e11 (u0 : M) : Prop := (t0 (e2) (e0 u0))
  let e12 (u0 : M) : Prop := (t0 (e10 u0) (e11 u0))
  have v0 : ((show Prop from (t0 (e3) ((show Prop from (t0 ((show Prop from (t1 (e1)))) (a2))))))) := p41 (a2) (e1)
  have v1 : (e9) := (show (e9) from v0)
  have v2 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p40 (a1 z0) (a2)
  have v3 : (∀ z0 : M, (e11 z0)) := fun z0 : M => b3 (e10 z0) (e11 z0) (v2 z0) (h0 z0)
  have v4 : (e3) := p338 (M := M) (e2) (fun w0 : M => (e0 w0)) ((fun w0 : M => v3 w0))
  have v5 : (e8) := b3 (e3) (e8) (v1) (v4)
  exact v5
-- Actual MMB 340 eqid
theorem p340 (a0 : M)  : (g342 (M := M) a0 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a0))
  let e1  : Prop := (t10 (M := M) (a0) (a0))
  let e2 (u0 : M) : Prop := (t0 (e0 u0) (e1))
  let e3 (u0 : M) : Prop := (t0 (e0 u0) (e2 u0))
  let e4 (u0 : M) : Prop := (t0 (e3 u0) (e2 u0))
  let e5  : Prop := (t9 (M := M) (fun x0_0 : M => (e0 x0_0)))
  have v0 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p33 (e0 z0) (e1)
  have v1 : (∀ z0 : M, (e3 z0)) := fun z0 : M => b331 (M := M) z0 (a0) (a0)
  have v2 : (∀ z0 : M, (e2 z0)) := fun z0 : M => b3 (e3 z0) (e2 z0) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t0 (e5) (e1)))) := p339 (M := M) (fun w0 : M => (e0 w0)) (e1) ((fun w0 : M => v2 w0))
  have v4 : (e5) := b330 (M := M) (a0)
  have v5 : (e1) := b3 (e5) (e1) (v3) (v4)
  exact v5
-- Actual MMB 341 eqcom
theorem p341 (a0 : M) (a1 : M)  : (g343 (M := M) a0 a1 ) := by
  let e0  : Prop := (t10 (M := M) (a0) (a0))
  let e1  : Prop := (t10 (M := M) (a0) (a1))
  let e2  : Prop := (t10 (M := M) (a1) (a0))
  have v0 : (e0) := p340 (M := M) (a0)
  have v1 : ((show Prop from (t0 (e1) ((show Prop from (t0 (e0) (e2))))))) := b331 (M := M) (a0) (a1) (a0)
  have v2 : ((show Prop from (t0 (e1) (e2)))) := p7 (e1) (e0) (e2) (v0) (v1)
  exact v2
-- Actual MMB 342 eqtr
theorem p342 (a0 : M) (a1 : M) (a2 : M)  : (g344 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a0))
  let e3  : Prop := (t0 ((show Prop from (t10 (M := M) (a1) (a2)))) ((show Prop from (t10 (M := M) (a0) (a2)))))
  let e5  : Prop := (t10 (M := M) (a0) (a1))
  have v0 : ((show Prop from (t0 (e0) (e3)))) := b331 (M := M) (a1) (a0) (a2)
  have v1 : ((show Prop from (t0 (e5) (e0)))) := p341 (M := M) (a0) (a1)
  have v2 : ((show Prop from (t0 (e5) (e3)))) := p10 (e5) (e0) (e3) (v0) (v1)
  exact v2
-- Actual MMB 343 eqtr2
theorem p344 (a0 : M) (a1 : M) (a2 : M)  : (g346 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t10 (M := M) (a2) (a1))
  let e1  : Prop := (t10 (M := M) (a1) (a2))
  let e3  : Prop := (t10 (M := M) (a0) (a1))
  let e4  : Prop := (t10 (M := M) (a0) (a2))
  have v0 : ((show Prop from (t0 (e0) (e1)))) := p341 (M := M) (a2) (a1)
  have v1 : ((show Prop from (t0 (e3) ((show Prop from (t0 (e1) (e4))))))) := p342 (M := M) (a0) (a1) (a2)
  have v2 : ((show Prop from (t0 (e3) ((show Prop from (t0 (e0) (e4))))))) := p17 (e3) (e0) (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 345 eqcomb
theorem p345 (a0 : M) (a1 : M)  : (g347 (M := M) a0 a1 ) := by
  let e0  : Prop := (t10 (M := M) (a0) (a1))
  let e1  : Prop := (t10 (M := M) (a1) (a0))
  have v0 : ((show Prop from (t0 (e0) (e1)))) := p341 (M := M) (a0) (a1)
  have v1 : ((show Prop from (t0 (e1) (e0)))) := p341 (M := M) (a1) (a0)
  have v2 : ((show Prop from (t3 (e0) (e1)))) := p112 (e0) (e1) (v0) (v1)
  exact v2
-- Actual MMB 346 eqeq1
theorem p346 (a0 : M) (a1 : M) (a2 : M)  : (g348 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t10 (M := M) (a0) (a1))
  let e1  : Prop := (t10 (M := M) (a0) (a2))
  let e2  : Prop := (t10 (M := M) (a1) (a2))
  have v0 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e1) (e2))))))) := p332 (M := M) (a1) (a0) (a2)
  have v1 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e2) (e1))))))) := p342 (M := M) (a0) (a1) (a2)
  have v2 : ((show Prop from (t0 (e0) ((show Prop from (t3 (e1) (e2))))))) := p113 (e0) (e1) (e2) (v0) (v1)
  exact v2
-- Actual MMB 347 eqeq2
theorem p347 (a0 : M) (a1 : M) (a2 : M)  : (g349 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t10 (M := M) (a0) (a1))
  let e1  : Prop := (t10 (M := M) (a1) (a2))
  let e2  : Prop := (t10 (M := M) (a0) (a2))
  have v0 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e1) (e2))))))) := Eq.trans
  have v1 : ((show Prop from (t0 (e1) ((show Prop from (t0 (e0) (e2))))))) := p23 _ _ _ (v0)
  have v2 : ((show Prop from (t0 (e2) ((show Prop from (t0 (e1) (e0))))))) := p344 (M := M) (a0) (a2) (a1)
  have v3 : ((show Prop from (t0 (e1) ((show Prop from (t0 (e2) (e0))))))) := p23 _ _ _ (v2)
  have v4 : ((show Prop from (t0 (e1) ((show Prop from (t3 (e0) (e2))))))) := p113 _ _ _ (v1) (v3)
  exact v4
-- Actual MMB 348 eqeq1d
theorem p348 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (g350 (M := M) a0 a1 a2 a3 )) : (g351 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  let e3  : Prop := (t3 ((show Prop from (t10 (M := M) (a1) (a3)))) ((show Prop from (t10 (M := M) (a2) (a3)))))
  have v0 : ((show Prop from (t0 (e0) (e3)))) := p346 (M := M) (a1) (a2) (a3)
  have v1 : ((show Prop from (t0 (a0) (e3)))) := p10 (a0) (e0) (e3) (v0) (h0)
  exact v1
-- Actual MMB 349 eqeq2d
theorem p349 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (g352 (M := M) a0 a1 a2 a3 )) : (g353 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t10 (M := M) (a2) (a3))
  let e3  : Prop := (t3 ((show Prop from (t10 (M := M) (a1) (a2)))) ((show Prop from (t10 (M := M) (a1) (a3)))))
  have v0 : ((show Prop from (t0 (e0) (e3)))) := p347 (M := M) (a1) (a2) (a3)
  have v1 : ((show Prop from (t0 (a0) (e3)))) := p10 (a0) (e0) (e3) (v0) (h0)
  exact v1
-- Actual MMB 350 eqeqd
theorem p350 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M) (h0 : (g354 (M := M) a0 a1 a2 a3 a4 )) (h1 : (g355 (M := M) a0 a1 a2 a3 a4 )) : (g356 (M := M) a0 a1 a2 a3 a4 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a3))
  let e1  : Prop := (t10 (M := M) (a2) (a3))
  let e4  : Prop := (t10 (M := M) (a2) (a4))
  have v0 : ((show Prop from (t0 (a0) ((show Prop from (t3 (e0) (e1))))))) := p348 (M := M) (a0) (a1) (a2) (a3) (h0)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t3 (e1) (e4))))))) := p349 (M := M) (a0) (a2) (a3) (a4) (h1)
  have v2 : ((show Prop from (t0 (a0) ((show Prop from (t3 (e0) (e4))))))) := p145 (a0) (e0) (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 351 eqeq
theorem p351 (a0 : M) (a1 : M) (a2 : M) (a3 : M)  : (g357 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t10 (M := M) (a0) (a1))
  let e1  : Prop := (t10 (M := M) (a2) (a3))
  let e2  : Prop := (t2 (e0) (e1))
  let e7  : Prop := (t3 ((show Prop from (t10 (M := M) (a0) (a2)))) ((show Prop from (t10 (M := M) (a1) (a3)))))
  have v0 : ((show Prop from (t0 (e2) (e0)))) := p53 _ _
  have v1 : ((show Prop from (t0 (e2) (e1)))) := p54 _ _
  have v2 : ((show Prop from (t0 (e2) (e7)))) := p350 (M := M) _ (a0) (a1) (a2) (a3) (v0) (v1)
  have v3 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e1) (e7))))))) := p84 _ _ _ (v2)
  exact v3
-- Actual MMB 352 eqtr2d
theorem p353 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (g359 (M := M) a0 a1 a2 a3 )) (h1 : (g352 (M := M) a0 a1 a2 a3 )) : (g360 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t10 (M := M) (a2) (a1))
  let e1  : Prop := (t10 (M := M) (a2) (a3))
  let e2  : Prop := (t10 (M := M) (a1) (a3))
  have v0 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e1) (e2))))))) := p332 (M := M) (a1) (a2) (a3)
  have v1 : ((show Prop from (t0 (a0) (e2)))) := p15 (a0) (e0) (e1) (e2) (v0) (h0) (h1)
  exact v1
-- Actual MMB 354 eqidd
theorem p354 (a0 : Prop) (a1 : M)  : (g361 (M := M) a0 a1 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a1))
  have v0 : (e0) := p340 (M := M) (a1)
  have v1 : ((show Prop from (t0 (a0) (e0)))) := p4 (a0) (e0) (v0)
  exact v1
-- Actual MMB 355 eqcomi
theorem p356 (a0 : Prop) (a1 : M) (a2 : M) (h0 : (g364 (M := M) a0 a1 a2 )) : (g365 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  let e1  : Prop := (t10 (M := M) (a2) (a1))
  have v0 : ((show Prop from (t0 (e0) (e1)))) := p341 (M := M) (a1) (a2)
  have v1 : ((show Prop from (t0 (a0) (e1)))) := p10 (a0) (e0) (e1) (v0) (h0)
  exact v1
-- Actual MMB 357 eqtrd
theorem p357 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (g350 (M := M) a0 a1 a2 a3 )) (h1 : (g352 (M := M) a0 a1 a2 a3 )) : (g360 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  let e1  : Prop := (t10 (M := M) (a2) (a3))
  let e2  : Prop := (t10 (M := M) (a1) (a3))
  have v0 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e1) (e2))))))) := p342 (M := M) (a1) (a2) (a3)
  have v1 : ((show Prop from (t0 (a0) (e2)))) := p15 (a0) (e0) (e1) (e2) (v0) (h0) (h1)
  exact v1
-- Actual MMB 358 eqtr4i
theorem p359 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (g350 (M := M) a0 a1 a2 a3 )) (h1 : (g369 (M := M) a0 a1 a2 a3 )) : (g360 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  let e1  : Prop := (t10 (M := M) (a3) (a2))
  let e2  : Prop := (t10 (M := M) (a1) (a3))
  have v0 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e1) (e2))))))) := p344 (M := M) (a1) (a2) (a3)
  have v1 : ((show Prop from (t0 (a0) (e2)))) := p15 (a0) (e0) (e1) (e2) (v0) (h0) (h1)
  exact v1
-- Actual MMB 360 syl5eq
theorem p360 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (g370 (M := M) a0 a1 a2 a3 )) (h1 : (g352 (M := M) a0 a1 a2 a3 )) : (g360 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  have v0 : ((show Prop from (t0 (a0) (e0)))) := p4 (a0) (e0) (h0)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t10 (M := M) (a1) (a3))))))) := p357 (M := M) (a0) (a1) (a2) (a3) (v0) (h1)
  exact v1
-- Actual MMB 361 syl5eqr
theorem p361 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (g371 (M := M) a0 a1 a2 a3 )) (h1 : (g352 (M := M) a0 a1 a2 a3 )) : (g360 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t10 (M := M) (a2) (a1))
  have v0 : ((show Prop from (t0 (a0) (e0)))) := p4 (a0) (e0) (h0)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t10 (M := M) (a1) (a3))))))) := p353 (M := M) (a0) (a1) (a2) (a3) (v0) (h1)
  exact v1
-- Actual MMB 362 syl6eq
theorem p362 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (g372 (M := M) a0 a1 a2 a3 )) (h1 : (g350 (M := M) a0 a1 a2 a3 )) : (g360 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t10 (M := M) (a2) (a3))
  have v0 : ((show Prop from (t0 (a0) (e0)))) := p4 (a0) (e0) (h0)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t10 (M := M) (a1) (a3))))))) := p357 (M := M) (a0) (a1) (a2) (a3) (h1) (v0)
  exact v1
-- Actual MMB 363 syl6eqr
theorem p363 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (g373 (M := M) a0 a1 a2 a3 )) (h1 : (g350 (M := M) a0 a1 a2 a3 )) : (g360 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t10 (M := M) (a3) (a2))
  have v0 : ((show Prop from (t0 (a0) (e0)))) := p4 (a0) (e0) (h0)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t10 (M := M) (a1) (a3))))))) := p359 (M := M) (a0) (a1) (a2) (a3) (h1) (v0)
  exact v1
-- Actual MMB 364 eqtr3g
theorem p365 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M) (h0 : (g376 (M := M) a0 a1 a2 a3 a4 )) (h1 : (g377 (M := M) a0 a1 a2 a3 a4 )) (h2 : (g354 (M := M) a0 a1 a2 a3 a4 )) : (g355 (M := M) a0 a1 a2 a3 a4 ) := by
  have v0 : ((show Prop from (t0 (a0) ((show Prop from (t10 (M := M) (a1) (a4))))))) := p363 (M := M) (a0) (a1) (a2) (a4) (h1) (h2)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t10 (M := M) (a3) (a4))))))) := p360 (M := M) (a0) (a3) (a1) (a4) (h0) (v0)
  exact v1
-- Actual MMB 366 aleq
theorem p366 (a1 : M → Prop) (a2 : M → Prop)  : (g378 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t0 (a1 u0) (a2 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e2  : Prop := (t8 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (a2 x0_0)))
  let e4  : Prop := (t0 (e2) (e3))
  let e6 (u0 : M) : Prop := (t3 (a1 u0) (a2 u0))
  let e7 (u0 : M) : Prop := (t0 (e6 u0) (e0 u0))
  let e8  : Prop := (t8 (M := M) (fun x0_0 : M => (e6 x0_0)))
  let e11 (u0 : M) : Prop := (t0 (a2 u0) (a1 u0))
  let e12  : Prop := (t8 (M := M) (fun x0_0 : M => (e11 x0_0)))
  let e13  : Prop := (t0 (e3) (e2))
  let e15 (u0 : M) : Prop := (t0 (e6 u0) (e11 u0))
  have v0 : ((show Prop from (t0 (e1) (e4)))) := b326 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (a2 w0))
  have v1 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p104 _ _
  have v2 : ((show Prop from (t0 (e8) (e1)))) := p337 (M := M) (fun w0 : M => (e6 w0)) (fun w0 : M => (e0 w0)) ((fun w0 : M => v1 w0))
  have v3 : ((show Prop from (t0 (e8) (e4)))) := p10 _ _ _ (v0) (v2)
  have v4 : ((show Prop from (t0 (e12) (e13)))) := b326 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (a1 w0))
  have v5 : (∀ z0 : M, (e15 z0)) := fun z0 : M => p108 _ _
  have v6 : ((show Prop from (t0 (e8) (e12)))) := p337 (M := M) (fun w0 : M => (e6 w0)) (fun w0 : M => (e11 w0)) ((fun w0 : M => v5 w0))
  have v7 : ((show Prop from (t0 (e8) (e13)))) := p10 _ _ _ (v4) (v6)
  have v8 : ((show Prop from (t0 (e8) ((show Prop from (t3 (e2) (e3))))))) := p113 _ _ _ (v3) (v7)
  exact v8
-- Actual MMB 367 aleqi
theorem p367 (a1 : M → Prop) (a2 : M → Prop) (h0 : (∀ z0 : M, (g379 (M := M) a1 a2 z0))) : (g380 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t3 (a1 u0) (a2 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4  : Prop := (t3 ((show Prop from (t8 (M := M) (fun x0_0 : M => (a1 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (a2 x0_0))))))
  have v0 : ((show Prop from (t0 (e1) (e4)))) := p366 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (a2 w0))
  have v1 : (e1) := b325 (M := M) (fun w0 : M => (e0 w0)) ((fun w0 : M => h0 w0))
  have v2 : (e4) := b3 (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 368 alimd
theorem p368 (a1 : Prop) (a2 : M → Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (g381 (M := M) a1 a2 a3 z0))) : (g382 (M := M) a1 a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t0 (a2 u0) (a3 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4  : Prop := (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (a3 x0_0))))))
  let e6  : Prop := (t8 (M := M) (fun x0_0 : M => (a1)))
  have v0 : ((show Prop from (t0 (e1) (e4)))) := b326 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3 w0))
  have v1 : ((show Prop from (t0 (e6) (e1)))) := p337 (M := M) (fun w0 : M => (a1)) (fun w0 : M => (e0 w0)) ((fun w0 : M => h0 w0))
  have v2 : ((show Prop from (t0 (a1) (e6)))) := b328 (M := M) (a1)
  have v3 : ((show Prop from (t0 (a1) (e1)))) := p10 _ _ _ (v1) (v2)
  have v4 : ((show Prop from (t0 (a1) (e4)))) := p10 _ _ _ (v0) (v3)
  exact v4
-- Actual MMB 369 raleqi
theorem p370 (a1 : M → Prop) (a2 : M → Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (g385 (M := M) a1 a2 a3 z0))) : (g386 (M := M) a1 a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t0 (a2 u0) (a3 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4  : Prop := (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (a3 x0_0))))))
  let e6  : Prop := (t8 (M := M) (fun x0_0 : M => (a1 x0_0)))
  have v0 : ((show Prop from (t0 (e1) (e4)))) := b326 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3 w0))
  have v1 : ((show Prop from (t0 (e6) (e1)))) := p337 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (e0 w0)) ((fun w0 : M => h0 w0))
  have v2 : ((show Prop from (t0 (e6) (e4)))) := p10 (e6) (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 371 aleqd
theorem p371 (a0 : Prop) (a2 : M → Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (g387 (M := M) a0 a2 a3 z0))) : (g388 (M := M) a0 a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t3 (a2 u0) (a3 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4  : Prop := (t3 ((show Prop from (t8 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (a3 x0_0))))))
  have v0 : ((show Prop from (t0 (e1) (e4)))) := p366 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3 w0))
  have v1 : ((show Prop from (t0 (a0) (e1)))) := p338 (M := M) (a0) (fun w0 : M => (e0 w0)) ((fun w0 : M => h0 w0))
  have v2 : ((show Prop from (t0 (a0) (e4)))) := p10 (a0) (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 372 ialda
theorem p372 (a1 : Prop) (a2 : M → Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (g389 (M := M) a1 a2 a3 z0))) : (g390 (M := M) a1 a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t0 (a2 u0) (a3 u0))
  let e1 (u0 : M) : Prop := (t0 (a1) (e0 u0))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p84 (a1) (a2 z0) (a3 z0) (h0 z0)
  have v1 : ((show Prop from (t0 (a1) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))))))) := p338 (M := M) (a1) (fun w0 : M => (e0 w0)) ((fun w0 : M => v0 w0))
  exact v1
-- Actual MMB 373 alcomb
theorem p373 (a2 : M → M → Prop)  : (g391 (M := M) a2 ) := by
  let e0 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (a2 u0 x0_0)))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e2 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (a2 x0_0 u0)))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (e2 x0_0)))
  have v0 : ((show Prop from (t0 (e1) (e3)))) := b334 (M := M) (fun w0 : M => (fun w1 : M => (a2 w0 w1)))
  have v1 : ((show Prop from (t0 (e3) (e1)))) := b334 (M := M) (fun w0 : M => (fun w1 : M => (a2 w1 w0)))
  have v2 : ((show Prop from (t3 (e1) (e3)))) := p112 (e1) (e3) (v0) (v1)
  exact v2
-- Actual MMB 374 alan
theorem p376 (a1 : M → Prop) (a2 : M → Prop)  : (g394 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t1 (a2 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e2 (u0 : M) : Prop := (t1 (a1 u0))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e4  : Prop := (t0 (e1) (e3))
  let e11  : Prop := (t0 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a1 x0_0))))) ((show Prop from (t9 (M := M) (fun x0_0 : M => (a2 x0_0))))))
  let e12  : Prop := (t0 (e4) (e11))
  let e13 (u0 : M) : Prop := (t0 (a1 u0) (a2 u0))
  let e14 (u0 : M) : Prop := (t0 (e0 u0) (e2 u0))
  let e15 (u0 : M) : Prop := (t0 (e13 u0) (e14 u0))
  let e16  : Prop := (t8 (M := M) (fun x0_0 : M => (e13 x0_0)))
  have v0 : ((show Prop from (t0 (e4) ((show Prop from (t0 ((show Prop from (t1 (e3)))) ((show Prop from (t1 (e1)))))))))) := p40 _ _
  have v1 : (e12) := (show (e12) from v0)
  have v2 : (∀ z0 : M, (e15 z0)) := fun z0 : M => p40 _ _
  have v3 : ((show Prop from (t0 (e16) (e4)))) := p370 (M := M) (fun w0 : M => (e13 w0)) (fun w0 : M => (e0 w0)) (fun w0 : M => (e2 w0)) ((fun w0 : M => v2 w0))
  have v4 : ((show Prop from (t0 (e16) (e11)))) := p10 _ _ _ (v1) (v3)
  exact v4
-- Actual MMB 377 eximi
theorem p377 (a1 : M → Prop) (a2 : M → Prop) (h0 : (∀ z0 : M, (g336 (M := M) a1 a2 z0))) : (g395 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t0 (a1 u0) (a2 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4  : Prop := (t0 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a1 x0_0))))) ((show Prop from (t9 (M := M) (fun x0_0 : M => (a2 x0_0))))))
  have v0 : ((show Prop from (t0 (e1) (e4)))) := p376 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (a2 w0))
  have v1 : (e1) := b325 (M := M) (fun w0 : M => (e0 w0)) ((fun w0 : M => h0 w0))
  have v2 : (e4) := b3 (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 378 exeq
theorem p378 (a1 : M → Prop) (a2 : M → Prop)  : (g396 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t1 (a1 u0))
  let e1 (u0 : M) : Prop := (t1 (a2 u0))
  let e2 (u0 : M) : Prop := (t3 (e0 u0) (e1 u0))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e4  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e5  : Prop := (t8 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e6  : Prop := (t3 (e4) (e5))
  let e8 (u0 : M) : Prop := (t3 (a1 u0) (a2 u0))
  let e9 (u0 : M) : Prop := (t0 (e8 u0) (e2 u0))
  let e10  : Prop := (t8 (M := M) (fun x0_0 : M => (e8 x0_0)))
  let e20  : Prop := (t0 (e10) ((show Prop from (t3 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a1 x0_0))))) ((show Prop from (t9 (M := M) (fun x0_0 : M => (a2 x0_0)))))))))
  have v0 : ((show Prop from (t0 (e3) (e6)))) := p366 (M := M) (fun w0 : M => (e0 w0)) (fun w0 : M => (e1 w0))
  have v1 : (∀ z0 : M, (e9 z0)) := fun z0 : M => p185 _ _
  have v2 : ((show Prop from (t0 (e10) (e3)))) := p337 (M := M) (fun w0 : M => (e8 w0)) (fun w0 : M => (e2 w0)) ((fun w0 : M => v1 w0))
  have v3 : ((show Prop from (t0 (e10) (e6)))) := p10 _ _ _ (v0) (v2)
  have v4 : ((show Prop from (t0 (e10) ((show Prop from (t3 ((show Prop from (t1 (e4)))) ((show Prop from (t1 (e5)))))))))) := p187 _ _ _ (v3)
  have v5 : (e20) := (show (e20) from v4)
  exact v5
-- Actual MMB 379 exeqd
theorem p379 (a0 : Prop) (a2 : M → Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (g387 (M := M) a0 a2 a3 z0))) : (g397 (M := M) a0 a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t3 (a2 u0) (a3 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4  : Prop := (t3 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show Prop from (t9 (M := M) (fun x0_0 : M => (a3 x0_0))))))
  have v0 : ((show Prop from (t0 (e1) (e4)))) := p378 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3 w0))
  have v1 : ((show Prop from (t0 (a0) (e1)))) := p338 (M := M) (a0) (fun w0 : M => (e0 w0)) ((fun w0 : M => h0 w0))
  have v2 : ((show Prop from (t0 (a0) (e4)))) := p10 (a0) (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 380 exeqi
theorem p380 (a1 : M → Prop) (a2 : M → Prop) (h0 : (∀ z0 : M, (g379 (M := M) a1 a2 z0))) : (g398 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t3 (a1 u0) (a2 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4  : Prop := (t3 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a1 x0_0))))) ((show Prop from (t9 (M := M) (fun x0_0 : M => (a2 x0_0))))))
  have v0 : ((show Prop from (t0 (e1) (e4)))) := p378 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (a2 w0))
  have v1 : (e1) := b325 (M := M) (fun w0 : M => (e0 w0)) ((fun w0 : M => h0 w0))
  have v2 : (e4) := b3 (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 381 rexeqi
theorem p385 (a1 : M → Prop)  : (∀ z0 : M, (g404 (M := M) a1 z0)) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e1 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e2 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e1 u0 u1))
  let e3 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (e1 u0 x0_0)))
  let e4 (u0 : M) (u1 : M) : Prop := (t0 (e1 u0 u1) (a1 u1))
  let e5 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e4 u0 x0_0)))
  let e6  : Prop := (t9 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e7 (u0 : M) : Prop := (t0 (e3 u0) (e6))
  let e8 (u0 : M) : Prop := (t0 (e5 u0) (e7 u0))
  let e9 (u0 : M) : Prop := (t0 (e5 u0) (e6))
  let e10 (u0 : M) (u1 : M) : Prop := (t0 (a1 u1) (e5 u0))
  let e11 (u0 : M) (u1 : M) : Prop := (t0 (e1 u0 u1) (e10 u0 u1))
  let e12 (u0 : M) : Prop := (t0 (a1 u0) (e6))
  let e13 (u0 : M) (u1 : M) : Prop := (t0 (e1 u0 u1) (e12 u1))
  let e14 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e12 u1))
  let e15 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (e0 x0_0 u0)))
  let e16 (u0 : M) : Prop := (t0 (e15 u0) (e12 u0))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e2 z0 z1))) := fun z0 : M => fun z1 : M => p341 (M := M) z0 z1
  have v1 : (∀ z0 : M, (e3 z0)) := fun z0 : M => b330 (M := M) z0
  have v2 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p376 (M := M) (fun w0 : M => (e1 z0 w0)) (fun w0 : M => (a1 w0))
  have v3 : (∀ z0 : M, (e9 z0)) := fun z0 : M => p7 (e5 z0) (e3 z0) (e6) (v1 z0) (v2 z0)
  have v4 : (∀ z0 : M, (∀ z1 : M, (e11 z0 z1))) := fun z0 : M => fun z1 : M => b336 (M := M) z0 (fun w0 : M => (a1 w0)) z1
  have v5 : (∀ z0 : M, (∀ z1 : M, (e13 z0 z1))) := fun z0 : M => fun z1 : M => p18 (e1 z0 z1) (a1 z1) (e5 z0) (e6) (v3 z0) (v4 z0 z1)
  have v6 : (∀ z0 : M, (∀ z1 : M, (e14 z0 z1))) := fun z0 : M => fun z1 : M => p11 (e0 z0 z1) (e1 z0 z1) (e12 z1) (v0 z0 z1) (v5 z0 z1)
  have v7 : (∀ z0 : M, (e16 z0)) := fun z0 : M => p339 (M := M) (fun w0 : M => (e0 w0 z0)) (e12 z0) ((fun w0 : M => v6 w0 z0))
  have v8 : (∀ z0 : M, (e15 z0)) := fun z0 : M => b330 (M := M) z0
  have v9 : (∀ z0 : M, (e12 z0)) := fun z0 : M => b3 (e15 z0) (e12 z0) (v7 z0) (v8 z0)
  exact v9
-- Actual MMB 386 alanex
theorem p388 (a1 : M → Prop)  : (g407 (M := M) a1 ) := by
  let e0 (u0 : M) : Prop := (t1 (a1 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e7  : Prop := (t3 (e1) ((show Prop from (t1 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a1 x0_0)))))))))
  have v0 : ((show Prop from (t3 (e1) ((show Prop from (t1 ((show Prop from (t1 (e1)))))))))) := p137 (e1)
  have v1 : (e7) := (show (e7) from v0)
  exact v1
-- Actual MMB 389 ngen
theorem p389 (a1 : M → Prop) (h0 : (∀ z0 : M, (g408 (M := M) a1 z0))) : (g409 (M := M) a1 ) := by
  let e0 (u0 : M) : Prop := (t1 (a1 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e6  : Prop := (t1 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a1 x0_0))))))
  let e7  : Prop := (t0 (e1) (e6))
  have v0 : ((show Prop from (t0 (e1) ((show Prop from (t1 ((show Prop from (t1 (e1)))))))))) := p39 (e1)
  have v1 : (e7) := (show (e7) from v0)
  have v2 : (e1) := b325 (M := M) (fun w0 : M => (e0 w0)) ((fun w0 : M => h0 w0))
  have v3 : (e6) := b3 (e1) (e6) (v1) (v2)
  exact v3
-- Actual MMB 390 alex
theorem p390 (a1 : M → Prop)  : (g410 (M := M) a1 ) := by
  let e0  : Prop := (t8 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e1 (u0 : M) : Prop := (t1 (a1 u0))
  let e2 (u0 : M) : Prop := (t1 (e1 u0))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e5  : Prop := (t1 ((show Prop from (t9 (M := M) (fun x0_0 : M => (e1 x0_0))))))
  let e6  : Prop := (t3 (e0) (e3))
  let e7  : Prop := (t3 (e3) (e5))
  let e8  : Prop := (t3 (e0) (e5))
  let e9  : Prop := (t0 (e7) (e8))
  let e11 (u0 : M) : Prop := (t3 (a1 u0) (e2 u0))
  have v0 : ((show Prop from (t0 (e6) (e9)))) := p149 (e0) (e3) (e5)
  have v1 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p137 (a1 z0)
  have v2 : (e6) := p367 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (e2 w0)) ((fun w0 : M => v1 w0))
  have v3 : (e9) := b3 (e6) (e9) (v0) (v2)
  have v4 : (e7) := p388 (M := M) (fun w0 : M => (e1 w0))
  have v5 : (e8) := b3 (e7) (e8) (v3) (v4)
  exact v5
-- Actual MMB 391 exnal
theorem p391 (a1 : M → Prop)  : (g411 (M := M) a1 ) := by
  let e0  : Prop := (t8 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e1 (u0 : M) : Prop := (t1 (a1 u0))
  let e2  : Prop := (t9 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e4  : Prop := (t3 (e0) ((show Prop from (t1 (e2)))))
  let e6  : Prop := (t3 (e2) ((show Prop from (t1 (e0)))))
  have v0 : ((show Prop from (t0 (e4) (e6)))) := p128 (e0) (e2)
  have v1 : (e4) := p390 (M := M) (fun w0 : M => (a1 w0))
  have v2 : (e6) := b3 (e4) (e6) (v0) (v1)
  exact v2
-- Actual MMB 392 eal
theorem p392 (a1 : M → Prop)  : (∀ z0 : M, (g412 (M := M) a1 z0)) := by
  let e0  : Prop := (t8 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e1 (u0 : M) : Prop := (t1 (a1 u0))
  let e2  : Prop := (t1 (e0))
  let e3 (u0 : M) : Prop := (t0 (e1 u0) (e2))
  let e4 (u0 : M) : Prop := (t0 (e0) (a1 u0))
  let e5 (u0 : M) : Prop := (t0 (e3 u0) (e4 u0))
  let e6  : Prop := (t9 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e8 (u0 : M) : Prop := (t0 (e1 u0) (e6))
  have v0 : (∀ z0 : M, (e5 z0)) := fun z0 : M => b2 (a1 z0) (e0)
  have v1 : ((show Prop from (t3 (e6) (e2)))) := p391 (M := M) (fun w0 : M => (a1 w0))
  have v2 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p385 (M := M) (fun w0 : M => (e1 w0)) z0
  have v3 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p153 (e1 z0) (e6) (e2) (v1) (v2 z0)
  have v4 : (∀ z0 : M, (e4 z0)) := fun z0 : M => b3 (e3 z0) (e4 z0) (v0 z0) (v3 z0)
  exact v4
-- Actual MMB 393 albi
theorem p398 (a1 : Prop) (a2 : M → Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (g381 (M := M) a1 a2 a3 z0))) : (g418 (M := M) a1 a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t0 (a2 u0) (a3 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4  : Prop := (t0 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show Prop from (t9 (M := M) (fun x0_0 : M => (a3 x0_0))))))
  have v0 : ((show Prop from (t0 (e1) (e4)))) := p376 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3 w0))
  have v1 : ((show Prop from (t0 (a1) (e1)))) := p338 (M := M) (a1) (fun w0 : M => (e0 w0)) ((fun w0 : M => h0 w0))
  have v2 : ((show Prop from (t0 (a1) (e4)))) := p10 (a1) (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 399 excomb
theorem p404 (a0 : Prop) (a2 : M → Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (g387 (M := M) a0 a2 a3 z0))) : (g424 (M := M) a0 a2 a3 ) := by
  let e0  : Prop := (t8 (M := M) (fun x0_0 : M => (a2 x0_0)))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (a3 x0_0)))
  let e4 (u0 : M) : Prop := (t0 (a2 u0) (e0))
  let e5 (u0 : M) : Prop := (t0 (a3 u0) (e1))
  let e6 (u0 : M) : Prop := (t3 (e4 u0) (e5 u0))
  let e7 (u0 : M) : Prop := (t0 (a0) (e6 u0))
  let e15  : Prop := (t0 (a0) ((show Prop from (t3 ((show Prop from (t11 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show Prop from (t11 (M := M) (fun x0_0 : M => (a3 x0_0)))))))))
  have v0 : ((show Prop from (t0 (a0) ((show Prop from (t3 (e0) (e1))))))) := p371 (M := M) _ (fun w1 : M => (a2 w1)) (fun w1 : M => (a3 w1)) ((fun w1 : M => h0 w1))
  have v1 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p188 _ _ _ _ _ (h0 z0) (v0)
  have v2 : ((show Prop from (t0 (a0) ((show Prop from (t3 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e4 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e5 x0_0))))))))))) := p371 (M := M) _ (fun w1 : M => (e4 w1)) (fun w1 : M => (e5 w1)) ((fun w1 : M => v1 w1))
  have v3 : (e15) := (show (e15) from v2)
  exact v3
-- Actual MMB 405 nfv
theorem p405 (a0 : Prop)  : (g425 (M := M) a0 ) := by
  let e1  : Prop := (t0 (a0) ((show Prop from (t8 (M := M) (fun x0_0 : M => (a0))))))
  let e3  : Prop := (t11 (M := M) (fun x0_0 : M => (a0)))
  have v0 : (e1) := b328 (M := M) (a0)
  have v1 : ((show Prop from (t8 (M := M) (fun x0_0 : M => (e1))))) := b325 (M := M) (fun w0 : M => (e1)) ((fun w0 : M => v0))
  have v2 : (e3) := (show (e3) from v1)
  exact v2
-- Actual MMB 406 nfi
theorem p406 (a1 : M → Prop) (h0 : (g426 (M := M) a1 )) : (∀ z0 : M, (g427 (M := M) a1 z0)) := by
  let e1 (u0 : M) : Prop := (t0 (a1 u0) ((show Prop from (t8 (M := M) (fun x0_0 : M => (a1 x0_0))))))
  let e2  : Prop := (t8 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e3 (u0 : M) : Prop := (t0 (e2) (e1 u0))
  have v0 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p392 (M := M) (fun w0 : M => (e1 w0)) z0
  have v1 : (e2) := (show (e2) from h0)
  have v2 : (∀ z0 : M, (e1 z0)) := fun z0 : M => b3 (e2) (e1 z0) (v0 z0) (v1)
  exact v2
-- Actual MMB 407 nfri
theorem p407 (a1 : M → Prop) (h0 : (∀ z0 : M, (g427 (M := M) a1 z0))) : (g426 (M := M) a1 ) := by
  let e1 (u0 : M) : Prop := (t0 (a1 u0) ((show Prop from (t8 (M := M) (fun x0_0 : M => (a1 x0_0))))))
  let e3  : Prop := (t11 (M := M) (fun x0_0 : M => (a1 x0_0)))
  have v0 : ((show Prop from (t8 (M := M) (fun x0_0 : M => (e1 x0_0))))) := b325 (M := M) (fun w0 : M => (e1 w0)) ((fun w0 : M => h0 w0))
  have v1 : (e3) := (show (e3) from v0)
  exact v1
-- Actual MMB 408 nfeqi
theorem p408 (a1 : M → Prop) (a2 : M → Prop) (h0 : (∀ z0 : M, (g379 (M := M) a1 a2 z0))) : (g428 (M := M) a1 a2 ) := by
  let e0  : Prop := (t6)
  let e1 (u0 : M) : Prop := (t3 (a1 u0) (a2 u0))
  let e2 (u0 : M) : Prop := (t0 (e0) (e1 u0))
  let e5  : Prop := (t3 ((show Prop from (t11 (M := M) (fun x0_0 : M => (a1 x0_0))))) ((show Prop from (t11 (M := M) (fun x0_0 : M => (a2 x0_0))))))
  have v0 : (∀ z0 : M, (e2 z0)) := fun z0 : M => p4 (e0) (e1 z0) (h0 z0)
  have v1 : ((show Prop from (t0 (e0) (e5)))) := p404 (M := M) (e0) (fun w1 : M => (a1 w1)) (fun w1 : M => (a2 w1)) ((fun w1 : M => v0 w1))
  have v2 : (e5) := p318 (e5) (v1)
  exact v2
-- Actual MMB 409 nfx
theorem p409 (a1 : M → Prop) (a2 : M → Prop) (h0 : (∀ z0 : M, (g379 (M := M) a1 a2 z0))) (h1 : (g429 (M := M) a1 a2 )) : (g430 (M := M) a1 a2 ) := by
  let e0  : Prop := (t11 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e1  : Prop := (t11 (M := M) (fun x0_0 : M => (a2 x0_0)))
  have v0 : ((show Prop from (t3 (e0) (e1)))) := p408 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (a2 w0)) ((fun w0 : M => h0 w0))
  have v1 : ((show Prop from (t0 (e1) (e0)))) := p109 (e0) (e1) (v0)
  have v2 : (e0) := b3 (e1) (e0) (v1) (h1)
  exact v2
-- Actual MMB 410 nfal
theorem p410 (a2 : M → M → Prop) (h0 : (∀ z0 : M, (g431 (M := M) a2 z0))) : (g432 (M := M) a2 ) := by
  let e0 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (a2 x0_0 u0)))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e2 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (a2 u0 x0_0)))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e5 (u0 : M) (u1 : M) : Prop := (t0 (a2 u0 u1) (e0 u1))
  let e6 (u0 : M) : Prop := (t0 (e2 u0) (e1))
  let e7 (u0 : M) : Prop := (t0 (e2 u0) (e3))
  have v0 : ((show Prop from (t0 (e1) (e3)))) := b334 (M := M) (fun w0 : M => (fun w1 : M => (a2 w1 w0)))
  have v1 : (∀ z0 : M, (∀ z1 : M, (e5 z0 z1))) := fun z0 : M => fun z1 : M => p406 (M := M) (fun w0 : M => (a2 w0 z1)) (h0 z1) z0
  have v2 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p337 (M := M) (fun w0 : M => (a2 z0 w0)) (fun w0 : M => (e0 w0)) ((fun w0 : M => v1 z0 w0))
  have v3 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p10 (e2 z0) (e1) (e3) (v0) (v2 z0)
  have v4 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e2 x0_0))))) := p407 (M := M) (fun w0 : M => (e2 w0)) ((fun w0 : M => v3 w0))
  exact v4
-- Actual MMB 411 nfnot
theorem p411 (a1 : M → Prop) (h0 : (g426 (M := M) a1 )) : (g433 (M := M) a1 ) := by
  let e0 (u0 : M) : Prop := (t1 (a1 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e2  : Prop := (t1 (e1))
  let e3 (u0 : M) : Prop := (t0 (e2) (a1 u0))
  let e4 (u0 : M) : Prop := (t0 (e0 u0) (e1))
  let e5 (u0 : M) : Prop := (t0 (e3 u0) (e4 u0))
  let e6  : Prop := (t8 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e7 (u0 : M) : Prop := (t0 (e6) (a1 u0))
  let e8  : Prop := (t1 (e6))
  let e9  : Prop := (t8 (M := M) (fun x0_0 : M => (e8)))
  let e10  : Prop := (t0 (e8) (e9))
  let e11  : Prop := (t1 (e9))
  let e12  : Prop := (t0 (e11) (e6))
  let e14 (u0 : M) : Prop := (t0 (a1 u0) (e6))
  let e18  : Prop := (t0 (e2) (e11))
  have v0 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p41 _ _
  have v1 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p392 (M := M) (fun w0 : M => (a1 w0)) z0
  have v2 : ((show Prop from (t0 (e10) (e12)))) := p41 _ _
  have v3 : (e10) := b333 (M := M) (fun w0 : M => (a1 w0))
  have v4 : (e12) := ((v2) (v3))
  have v5 : (∀ z0 : M, (e14 z0)) := fun z0 : M => p406 (M := M) (fun w0 : M => (a1 w0)) (h0) z0
  have v6 : ((show Prop from (t0 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a1 x0_0))))) ((show Prop from (t9 (M := M) (fun x0_0 : M => (e6)))))))) := p377 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (e6)) ((fun w0 : M => v5 w0))
  have v7 : (e18) := (show (e18) from v6)
  have v8 : ((show Prop from (t0 (e2) (e6)))) := p10 _ _ _ (v4) (v7)
  have v9 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p10 _ _ _ (v1 z0) (v8)
  have v10 : (∀ z0 : M, (e4 z0)) := fun z0 : M => ((v0 z0) (v9 z0))
  have v11 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e0 x0_0))))) := p407 (M := M) (fun w0 : M => (e0 w0)) ((fun w0 : M => v10 w0))
  exact v11
-- Actual MMB 412 nfim
theorem p412 (a1 : M → Prop) (a2 : M → Prop) (h0 : (g430 (M := M) a1 a2 )) (h1 : (g429 (M := M) a1 a2 )) : (g434 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t0 (a1 u0) (a2 u0))
  let e1 (u0 : M) : Prop := (t0 (a2 u0) (e0 u0))
  let e2  : Prop := (t8 (M := M) (fun x0_0 : M => (a2 x0_0)))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e5 (u0 : M) : Prop := (t0 (a2 u0) (e2))
  let e6 (u0 : M) : Prop := (t0 (a2 u0) (e3))
  let e7 (u0 : M) : Prop := (t0 (e0 u0) (a2 u0))
  let e8 (u0 : M) : Prop := (t0 (a1 u0) (e7 u0))
  let e9 (u0 : M) : Prop := (t0 (e0 u0) (e3))
  let e10 (u0 : M) : Prop := (t0 (a1 u0) (e9 u0))
  let e11 (u0 : M) : Prop := (t1 (a1 u0))
  let e12 (u0 : M) : Prop := (t0 (e11 u0) (e0 u0))
  let e13  : Prop := (t8 (M := M) (fun x0_0 : M => (e11 x0_0)))
  let e16 (u0 : M) : Prop := (t0 (e11 u0) (e13))
  let e17 (u0 : M) : Prop := (t0 (e11 u0) (e3))
  let e18 (u0 : M) : Prop := (t0 (e11 u0) (e9 u0))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => b0 (a2 z0) (a1 z0)
  have v1 : ((show Prop from (t0 (e2) (e3)))) := p337 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (e0 w0)) ((fun w0 : M => v0 w0))
  have v2 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p406 (M := M) (fun w0 : M => (a2 w0)) (h1) z0
  have v3 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p10 (a2 z0) (e2) (e3) (v1) (v2 z0)
  have v4 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p24 (a1 z0) (a2 z0)
  have v5 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p18 (a1 z0) (e0 z0) (a2 z0) (e3) (v3 z0) (v4 z0)
  have v6 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p22 (a1 z0) (a2 z0)
  have v7 : ((show Prop from (t0 (e13) (e3)))) := p337 (M := M) (fun w0 : M => (e11 w0)) (fun w0 : M => (e0 w0)) ((fun w0 : M => v6 w0))
  have v8 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e11 x0_0))))) := p411 (M := M) (fun w0 : M => (a1 w0)) (h0)
  have v9 : (∀ z0 : M, (e16 z0)) := fun z0 : M => p406 (M := M) (fun w0 : M => (e11 w0)) (v8) z0
  have v10 : (∀ z0 : M, (e17 z0)) := fun z0 : M => p10 (e11 z0) (e13) (e3) (v7) (v9 z0)
  have v11 : (∀ z0 : M, (e18 z0)) := fun z0 : M => p12 (e11 z0) (e3) (e0 z0) (v10 z0)
  have v12 : (∀ z0 : M, (e9 z0)) := fun z0 : M => p42 (a1 z0) (e9 z0) (v5 z0) (v11 z0)
  have v13 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e0 x0_0))))) := p407 (M := M) (fun w0 : M => (e0 w0)) ((fun w0 : M => v12 w0))
  exact v13
-- Actual MMB 413 nfan
theorem p413 (a1 : M → Prop) (a2 : M → Prop) (h0 : (g430 (M := M) a1 a2 )) (h1 : (g429 (M := M) a1 a2 )) : (g435 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t1 (a2 u0))
  let e2 (u0 : M) : Prop := (t0 (a1 u0) (e0 u0))
  let e4 (u0 : M) : Prop := (t1 (e2 u0))
  let e6 (u0 : M) : Prop := (t2 (a1 u0) (a2 u0))
  let e7  : Prop := (t11 (M := M) (fun x0_0 : M => (e6 x0_0)))
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e0 x0_0))))) := p411 (M := M) (fun w0 : M => (a2 w0)) (h1)
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e2 x0_0))))) := p412 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (e0 w0)) (h0) (v0)
  have v2 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e4 x0_0))))) := p411 (M := M) (fun w0 : M => (e2 w0)) (v1)
  have v3 : (e7) := (show (e7) from v2)
  exact v3
-- Actual MMB 414 nfor
theorem p414 (a1 : M → Prop) (a2 : M → Prop) (h0 : (g430 (M := M) a1 a2 )) (h1 : (g429 (M := M) a1 a2 )) : (g436 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t1 (a1 u0))
  let e2 (u0 : M) : Prop := (t0 (e0 u0) (a2 u0))
  let e4 (u0 : M) : Prop := (t4 (a1 u0) (a2 u0))
  let e5  : Prop := (t11 (M := M) (fun x0_0 : M => (e4 x0_0)))
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e0 x0_0))))) := p411 (M := M) (fun w0 : M => (a1 w0)) (h0)
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e2 x0_0))))) := p412 (M := M) (fun w0 : M => (e0 w0)) (fun w0 : M => (a2 w0)) (v0) (h1)
  have v2 : (e5) := (show (e5) from v1)
  exact v2
-- Actual MMB 415 nfbi
theorem p415 (a1 : M → Prop) (a2 : M → Prop) (h0 : (g430 (M := M) a1 a2 )) (h1 : (g429 (M := M) a1 a2 )) : (g437 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t0 (a1 u0) (a2 u0))
  let e2 (u0 : M) : Prop := (t0 (a2 u0) (a1 u0))
  let e4 (u0 : M) : Prop := (t2 (e0 u0) (e2 u0))
  let e6 (u0 : M) : Prop := (t3 (a1 u0) (a2 u0))
  let e7  : Prop := (t11 (M := M) (fun x0_0 : M => (e6 x0_0)))
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e0 x0_0))))) := p412 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (a2 w0)) (h0) (h1)
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e2 x0_0))))) := p412 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (a1 w0)) (h1) (h0)
  have v2 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e4 x0_0))))) := p413 (M := M) (fun w0 : M => (e0 w0)) (fun w0 : M => (e2 w0)) (v0) (v1)
  have v3 : (e7) := (show (e7) from v2)
  exact v3
-- Actual MMB 416 nfex1
theorem p416 (a1 : M → Prop)  : (g438 (M := M) a1 ) := by
  let e0 (u0 : M) : Prop := (t1 (a1 u0))
  let e2  : Prop := (t1 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e0 x0_0))))))
  let e5  : Prop := (t9 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e7  : Prop := (t0 (e5) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e5))))))
  let e9  : Prop := (t11 (M := M) (fun x0_0 : M => (e5)))
  have v0 : ((show Prop from (t0 (e2) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e2)))))))) := b333 (M := M) (fun w0 : M => (e0 w0))
  have v1 : (e7) := (show (e7) from v0)
  have v2 : ((show Prop from (t8 (M := M) (fun x0_0 : M => (e7))))) := b325 (M := M) (fun w0 : M => (e7)) ((fun w0 : M => v1))
  have v3 : (e9) := (show (e9) from v2)
  exact v3
-- Actual MMB 417 nfex
theorem p417 (a2 : M → M → Prop) (h0 : (∀ z0 : M, (g431 (M := M) a2 z0))) : (g439 (M := M) a2 ) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t1 (a2 u0 u1))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 x0_0 u0)))
  let e2 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e0 u0 x0_0)))
  let e4 (u0 : M) : Prop := (t1 (e2 u0))
  let e6 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (a2 u0 x0_0)))
  let e7  : Prop := (t11 (M := M) (fun x0_0 : M => (e6 x0_0)))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p411 (M := M) (fun w0 : M => (a2 w0 z0)) (h0 z0)
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e2 x0_0))))) := p410 (M := M) (fun w0 : M => (fun w1 : M => (e0 w0 w1))) ((fun w1 : M => v0 w1))
  have v2 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e4 x0_0))))) := p411 (M := M) (fun w0 : M => (e2 w0)) (v1)
  have v3 : (e7) := (show (e7) from v2)
  exact v3
-- Actual MMB 418 nfal1
theorem p418 (a1 : M → Prop)  : (g440 (M := M) a1 ) := by
  let e0  : Prop := (t8 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e1 (u0 : M) : Prop := (t1 (a1 u0))
  let e2  : Prop := (t9 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e3  : Prop := (t1 (e2))
  have v0 : ((show Prop from (t3 (e0) (e3)))) := p390 (M := M) (fun w0 : M => (a1 w0))
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e2))))) := p416 (M := M) (fun w0 : M => (e1 w0))
  have v2 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e3))))) := p411 (M := M) (fun w0 : M => (e2)) (v1)
  have v3 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e0))))) := p409 (M := M) (fun w0 : M => (e0)) (fun w0 : M => (e3)) ((fun w0 : M => v0)) (v2)
  exact v3
-- Actual MMB 419 ialdh
theorem p419 (a1 : M → Prop) (a2 : M → Prop) (h0 : (g430 (M := M) a1 a2 )) (h1 : (∀ z0 : M, (g336 (M := M) a1 a2 z0))) : (∀ z0 : M, (g441 (M := M) a1 a2 z0)) := by
  let e0  : Prop := (t8 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (a2 x0_0)))
  let e3 (u0 : M) : Prop := (t0 (a1 u0) (e0))
  let e4 (u0 : M) : Prop := (t0 (a1 u0) (e1))
  have v0 : ((show Prop from (t0 (e0) (e1)))) := p337 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (a2 w0)) ((fun w0 : M => h1 w0))
  have v1 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p406 (M := M) (fun w0 : M => (a1 w0)) (h0) z0
  have v2 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p10 (a1 z0) (e0) (e1) (v0) (v1 z0)
  exact v2
-- Actual MMB 420 eexh
theorem p420 (a1 : M → Prop) (a2 : M → Prop) (h0 : (g429 (M := M) a1 a2 )) (h1 : (∀ z0 : M, (g336 (M := M) a1 a2 z0))) : (∀ z0 : M, (g442 (M := M) a1 a2 z0)) := by
  let e0 (u0 : M) : Prop := (t1 (a1 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e2 (u0 : M) : Prop := (t1 (a2 u0))
  let e3 (u0 : M) : Prop := (t0 (e2 u0) (e1))
  let e5 (u0 : M) : Prop := (t0 ((show Prop from (t1 (e1)))) (a2 u0))
  let e6 (u0 : M) : Prop := (t0 (e3 u0) (e5 u0))
  let e8 (u0 : M) : Prop := (t0 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a1 x0_0))))) (a2 u0))
  let e9 (u0 : M) : Prop := (t0 (e3 u0) (e8 u0))
  let e11 (u0 : M) : Prop := (t0 (a1 u0) (a2 u0))
  let e12 (u0 : M) : Prop := (t0 (e2 u0) (e0 u0))
  let e13 (u0 : M) : Prop := (t0 (e11 u0) (e12 u0))
  have v0 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p41 (a2 z0) (e1)
  have v1 : (∀ z0 : M, (e9 z0)) := (show (∀ z0 : M, (e9 z0)) from v0)
  have v2 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e2 x0_0))))) := p411 (M := M) (fun w0 : M => (a2 w0)) (h0)
  have v3 : (∀ z0 : M, (e13 z0)) := fun z0 : M => p40 (a1 z0) (a2 z0)
  have v4 : (∀ z0 : M, (e12 z0)) := fun z0 : M => b3 (e11 z0) (e12 z0) (v3 z0) (h1 z0)
  have v5 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p419 (M := M) (fun w0 : M => (e2 w0)) (fun w0 : M => (e0 w0)) (v2) ((fun w0 : M => v4 w0)) z0
  have v6 : (∀ z0 : M, (e8 z0)) := fun z0 : M => b3 (e3 z0) (e8 z0) (v1 z0) (v5 z0)
  exact v6
-- Actual MMB 421 eexdh
theorem p421 (a1 : M → Prop) (a2 : M → Prop) (a3 : M → Prop) (h0 : (g443 (M := M) a1 a2 a3 )) (h1 : (g444 (M := M) a1 a2 a3 )) (h2 : (∀ z0 : M, (g385 (M := M) a1 a2 a3 z0))) : (∀ z0 : M, (g445 (M := M) a1 a2 a3 z0)) := by
  let e0 (u0 : M) : Prop := (t1 (a3 u0))
  let e2 (u0 : M) : Prop := (t2 (a1 u0) (e0 u0))
  let e4 (u0 : M) : Prop := (t1 (a2 u0))
  let e5 (u0 : M) : Prop := (t0 (e0 u0) (e4 u0))
  let e6 (u0 : M) : Prop := (t0 (a1 u0) (e5 u0))
  let e7 (u0 : M) : Prop := (t0 (e2 u0) (e4 u0))
  let e8  : Prop := (t8 (M := M) (fun x0_0 : M => (e4 x0_0)))
  let e9 (u0 : M) : Prop := (t0 (e2 u0) (e8))
  let e10 (u0 : M) : Prop := (t0 (e0 u0) (e8))
  let e11 (u0 : M) : Prop := (t0 (a1 u0) (e10 u0))
  let e13 (u0 : M) : Prop := (t0 ((show Prop from (t1 (e8)))) (a3 u0))
  let e14 (u0 : M) : Prop := (t0 (a1 u0) (e13 u0))
  let e16 (u0 : M) : Prop := (t0 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a2 x0_0))))) (a3 u0))
  let e17 (u0 : M) : Prop := (t0 (a1 u0) (e16 u0))
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e0 x0_0))))) := p411 (M := M) (fun w0 : M => (a3 w0)) (h1)
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e2 x0_0))))) := p413 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (e0 w0)) (h0) (v0)
  have v2 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p46 (a1 z0) (a2 z0) (a3 z0) (h2 z0)
  have v3 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p83 (a1 z0) (e0 z0) (e4 z0) (v2 z0)
  have v4 : (∀ z0 : M, (e9 z0)) := fun z0 : M => p419 (M := M) (fun w0 : M => (e2 w0)) (fun w0 : M => (e4 w0)) (v1) ((fun w0 : M => v3 w0)) z0
  have v5 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p84 (a1 z0) (e0 z0) (e8) (v4 z0)
  have v6 : (∀ z0 : M, (e14 z0)) := fun z0 : M => p44 (a1 z0) (a3 z0) (e8) (v5 z0)
  have v7 : (∀ z0 : M, (e17 z0)) := (show (∀ z0 : M, (e17 z0)) from v6)
  exact v7
-- Actual MMB 422 alimdh
theorem p423 (a1 : M → Prop) (a2 : M → Prop) (a3 : M → Prop) (h0 : (g443 (M := M) a1 a2 a3 )) (h1 : (∀ z0 : M, (g400 (M := M) a1 a2 a3 z0))) : (∀ z0 : M, (g447 (M := M) a1 a2 a3 z0)) := by
  let e0 (u0 : M) : Prop := (t3 (a2 u0) (a3 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4  : Prop := (t3 ((show Prop from (t8 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (a3 x0_0))))))
  let e6 (u0 : M) : Prop := (t0 (a1 u0) (e1))
  let e7 (u0 : M) : Prop := (t0 (a1 u0) (e4))
  have v0 : ((show Prop from (t0 (e1) (e4)))) := p366 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3 w0))
  have v1 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p419 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (e0 w0)) (h0) ((fun w0 : M => h1 w0)) z0
  have v2 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p10 (a1 z0) (e1) (e4) (v0) (v1 z0)
  exact v2
-- Actual MMB 424 eexd
theorem p424 (a1 : Prop) (a2 : M → Prop) (a3 : Prop) (h0 : (∀ z0 : M, (g448 (M := M) a1 a2 a3 z0))) : (g449 (M := M) a1 a2 a3 ) := by
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (a1))))) := p405 (M := M) (a1)
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (a3))))) := p405 (M := M) (a3)
  have v2 : ((show Prop from (t0 (a1) ((show Prop from (t0 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a2 x0_0))))) (a3))))))) := p421 (M := M) (fun w0 : M => (a1)) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3)) (v0) (v1) ((fun w0 : M => h0 w0)) 0
  exact v2
-- Actual MMB 425 eexda
theorem p425 (a1 : Prop) (a2 : M → Prop) (a3 : Prop) (h0 : (∀ z0 : M, (g450 (M := M) a1 a2 a3 z0))) : (g449 (M := M) a1 a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t0 (a2 u0) (a3))
  let e1 (u0 : M) : Prop := (t0 (a1) (e0 u0))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p84 (a1) (a2 z0) (a3) (h0 z0)
  have v1 : ((show Prop from (t0 (a1) ((show Prop from (t0 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a2 x0_0))))) (a3))))))) := p424 (M := M) (a1) (fun w0 : M => (a2 w0)) (a3) ((fun w0 : M => v0 w0))
  exact v1
-- Actual MMB 426 eexb
theorem p426 (a1 : M → Prop) (a2 : Prop)  : (g451 (M := M) a1 a2 ) := by
  let e0  : Prop := (t9 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e3  : Prop := (t0 (e0) (a2))
  let e5 (u0 : M) : Prop := (t0 (a1 u0) (e0))
  let e6 (u0 : M) : Prop := (t0 (a1 u0) (a2))
  let e7 (u0 : M) : Prop := (t0 (e3) (e6 u0))
  let e8  : Prop := (t8 (M := M) (fun x0_0 : M => (e6 x0_0)))
  let e11 (u0 : M) : Prop := (t0 (e8) (e6 u0))
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e0))))) := p416 (M := M) (fun w0 : M => (a1 w0))
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (a2))))) := p405 (M := M) _
  have v2 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e3))))) := p412 (M := M) (fun w0 : M => (e0)) (fun w0 : M => (a2)) (v0) (v1)
  have v3 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p385 (M := M) (fun w0 : M => (a1 w0)) z0
  have v4 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p29 _ _ _ (v3 z0)
  have v5 : ((show Prop from (t0 (e3) (e8)))) := p419 (M := M) (fun w0 : M => (e3)) (fun w0 : M => (e6 w0)) (v2) ((fun w0 : M => v4 w0)) 0
  have v6 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e8))))) := p418 (M := M) (fun w0 : M => (e6 w0))
  have v7 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p392 (M := M) (fun w0 : M => (e6 w0)) z0
  have v8 : ((show Prop from (t0 (e8) (e3)))) := p421 (M := M) (fun w0 : M => (e8)) (fun w0 : M => (a1 w0)) (fun w0 : M => (a2)) (v6) (v1) ((fun w0 : M => v7 w0)) 0
  have v9 : ((show Prop from (t3 (e3) (e8)))) := p112 _ _ (v5) (v8)
  exact v9
-- Actual MMB 427 erexb
theorem p428 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (h0 : (g453 (M := M) a1 a2 a3 )) (h1 : (∀ z0 : M, (g454 (M := M) a1 a2 a3 z0))) : (∀ z0 : M, (g455 (M := M) a1 a2 a3 z0)) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1  : Prop := (t9 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e2 (u0 : M) : Prop := (t0 (e0 u0) (a2 u0))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e4  : Prop := (t9 (M := M) (fun x0_0 : M => (a2 x0_0)))
  let e5  : Prop := (t0 (e1) (e4))
  let e7 (u0 : M) : Prop := (t0 (a3 u0) (a2 u0))
  let e8 (u0 : M) : Prop := (t0 (e0 u0) (e7 u0))
  let e9 (u0 : M) : Prop := (t0 (a3 u0) (e2 u0))
  let e10 (u0 : M) : Prop := (t0 (a3 u0) (e3))
  let e11 (u0 : M) : Prop := (t0 (a3 u0) (e5))
  let e12 (u0 : M) : Prop := (t0 (a3 u0) (e4))
  have v0 : (e1) := b330 (M := M) (a1)
  have v1 : ((show Prop from (t0 (e3) (e5)))) := p376 (M := M) (fun w0 : M => (e0 w0)) (fun w0 : M => (a2 w0))
  have v2 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p110 (e0 z0) (a2 z0) (a3 z0) (h1 z0)
  have v3 : (∀ z0 : M, (e9 z0)) := fun z0 : M => p23 (e0 z0) (a3 z0) (a2 z0) (v2 z0)
  have v4 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p419 (M := M) (fun w0 : M => (a3 w0)) (fun w0 : M => (e2 w0)) (h0) ((fun w0 : M => v3 w0)) z0
  have v5 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p10 (a3 z0) (e3) (e5) (v1) (v4 z0)
  have v6 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p7 (a3 z0) (e1) (e4) (v0) (v5 z0)
  exact v6
-- Actual MMB 429 ealeh
theorem p429 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (h0 : (g453 (M := M) a1 a2 a3 )) (h1 : (∀ z0 : M, (g454 (M := M) a1 a2 a3 z0))) : (∀ z0 : M, (g456 (M := M) a1 a2 a3 z0)) := by
  let e0  : Prop := (t8 (M := M) (fun x0_0 : M => (a2 x0_0)))
  let e1 (u0 : M) : Prop := (t1 (a3 u0))
  let e2  : Prop := (t1 (e0))
  let e3 (u0 : M) : Prop := (t0 (e1 u0) (e2))
  let e4 (u0 : M) : Prop := (t0 (e0) (a3 u0))
  let e5 (u0 : M) : Prop := (t0 (e3 u0) (e4 u0))
  let e6 (u0 : M) : Prop := (t1 (a2 u0))
  let e7  : Prop := (t9 (M := M) (fun x0_0 : M => (e6 x0_0)))
  let e10 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e11 (u0 : M) : Prop := (t3 (e6 u0) (e1 u0))
  let e12 (u0 : M) : Prop := (t0 (e10 u0) (e11 u0))
  let e13 (u0 : M) : Prop := (t0 (e1 u0) (e7))
  have v0 : (∀ z0 : M, (e5 z0)) := fun z0 : M => b2 (a3 z0) (e0)
  have v1 : ((show Prop from (t3 (e7) (e2)))) := p391 (M := M) (fun w0 : M => (a2 w0))
  have v2 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e1 x0_0))))) := p411 (M := M) (fun w0 : M => (a3 w0)) (h0)
  have v3 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p187 (e10 z0) (a2 z0) (a3 z0) (h1 z0)
  have v4 : (∀ z0 : M, (e13 z0)) := fun z0 : M => p428 (M := M) (a1) (fun w0 : M => (e6 w0)) (fun w0 : M => (e1 w0)) (v2) ((fun w0 : M => v3 w0)) z0
  have v5 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p153 (e1 z0) (e7) (e2) (v1) (v4 z0)
  have v6 : (∀ z0 : M, (e4 z0)) := fun z0 : M => b3 (e3 z0) (e4 z0) (v0 z0) (v5 z0)
  exact v6
-- Actual MMB 430 alim1
theorem p440 (a1 : M) (a2 : M → Prop) (a3 : Prop) (h0 : (∀ z0 : M, (g468 (M := M) a1 a2 a3 z0))) : (g469 (M := M) a1 a2 a3 ) := by
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (a3))))) := p405 (M := M) (a3)
  have v1 : ((show Prop from (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (a2 x0_0))))) (a3)))) := p429 (M := M) (a1) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3)) (v0) ((fun w0 : M => h0 w0)) 0
  exact v1
-- Actual MMB 441 iexdeh
theorem p441 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (h0 : (g470 (M := M) a1 a2 a3 )) (h1 : (∀ z0 : M, (g471 (M := M) a1 a2 a3 z0))) : (∀ z0 : M, (g472 (M := M) a1 a2 a3 z0)) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1  : Prop := (t9 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e2 (u0 : M) : Prop := (t0 (e0 u0) (a3 u0))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e4  : Prop := (t9 (M := M) (fun x0_0 : M => (a3 x0_0)))
  let e5  : Prop := (t0 (e1) (e4))
  let e7 (u0 : M) : Prop := (t0 (a2 u0) (e2 u0))
  let e8 (u0 : M) : Prop := (t0 (a2 u0) (e3))
  let e9 (u0 : M) : Prop := (t0 (a2 u0) (e5))
  let e10 (u0 : M) : Prop := (t0 (a2 u0) (e4))
  have v0 : (e1) := b330 (M := M) (a1)
  have v1 : ((show Prop from (t0 (e3) (e5)))) := p376 (M := M) (fun w0 : M => (e0 w0)) (fun w0 : M => (a3 w0))
  have v2 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p84 (a2 z0) (e0 z0) (a3 z0) (h1 z0)
  have v3 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p419 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (e2 w0)) (h0) ((fun w0 : M => v2 w0)) z0
  have v4 : (∀ z0 : M, (e9 z0)) := fun z0 : M => p10 (a2 z0) (e3) (e5) (v1) (v3 z0)
  have v5 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p7 (a2 z0) (e1) (e4) (v0) (v4 z0)
  exact v5
-- Actual MMB 442 iexde
theorem p442 (a1 : Prop) (a2 : M) (a3 : M → Prop) (h0 : (∀ z0 : M, (g473 (M := M) a1 a2 a3 z0))) : (g474 (M := M) a1 a2 a3 ) := by
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (a1))))) := p405 (M := M) (a1)
  have v1 : ((show Prop from (t0 (a1) ((show Prop from (t9 (M := M) (fun x0_0 : M => (a3 x0_0)))))))) := p441 (M := M) (a2) (fun w0 : M => (a1)) (fun w0 : M => (a3 w0)) (v0) ((fun w0 : M => h0 w0)) 0
  exact v1
-- Actual MMB 443 iexdde
theorem p444 (a1 : M) (a2 : M → Prop) (h0 : (∀ z0 : M, (g477 (M := M) a1 a2 z0))) : (g478 (M := M) a1 a2 ) := by
  let e0  : Prop := (t6)
  let e1 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e2 (u0 : M) : Prop := (t2 (e0) (e1 u0))
  let e3 (u0 : M) : Prop := (t0 (e2 u0) (a2 u0))
  let e4  : Prop := (t9 (M := M) (fun x0_0 : M => (a2 x0_0)))
  have v0 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p63 (e0) (e1 z0) (a2 z0) (h0 z0)
  have v1 : ((show Prop from (t0 (e0) (e4)))) := p442 (M := M) (e0) (a1) (fun w0 : M => (a2 w0)) ((fun w0 : M => v0 w0))
  have v2 : (e4) := p318 (e4) (v1)
  exact v2
-- Actual MMB 445 iexe
theorem p445 (a1 : M) (a2 : M → Prop) (a3 : Prop) (h0 : (∀ z0 : M, (g468 (M := M) a1 a2 a3 z0))) : (g479 (M := M) a1 a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t3 (a2 u0) (a3))
  let e2 (u0 : M) : Prop := (t2 (a3) (e0 u0))
  let e3 (u0 : M) : Prop := (t0 (e2 u0) (e1 u0))
  let e4 (u0 : M) : Prop := (t0 (e2 u0) (a3))
  let e5 (u0 : M) : Prop := (t0 (e2 u0) (a2 u0))
  have v0 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p63 (a3) (e0 z0) (e1 z0) (h0 z0)
  have v1 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p53 (a3) (e0 z0)
  have v2 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p120 (e2 z0) (a3) (a2 z0) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t0 (a3) ((show Prop from (t9 (M := M) (fun x0_0 : M => (a2 x0_0)))))))) := p442 (M := M) (a3) (a1) (fun w0 : M => (a2 w0)) ((fun w0 : M => v2 w0))
  exact v3
-- Actual MMB 446 ealdeh
theorem p446 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (a4 : M → Prop) (h0 : (g480 (M := M) a1 a2 a3 a4 )) (h1 : (g481 (M := M) a1 a2 a3 a4 )) (h2 : (∀ z0 : M, (g482 (M := M) a1 a2 a3 a4 z0))) : (∀ z0 : M, (g483 (M := M) a1 a2 a3 a4 z0)) := by
  let e0 (u0 : M) : Prop := (t1 (a3 u0))
  let e1  : Prop := (t9 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e2  : Prop := (t8 (M := M) (fun x0_0 : M => (a3 x0_0)))
  let e3  : Prop := (t1 (e2))
  let e5 (u0 : M) : Prop := (t1 (a4 u0))
  let e7 (u0 : M) : Prop := (t2 (a2 u0) (e5 u0))
  let e9 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e10 (u0 : M) : Prop := (t2 (a2 u0) (e9 u0))
  let e11 (u0 : M) : Prop := (t0 (e5 u0) (e0 u0))
  let e12 (u0 : M) : Prop := (t0 (e10 u0) (e11 u0))
  let e13 (u0 : M) : Prop := (t2 (e10 u0) (e5 u0))
  let e14 (u0 : M) : Prop := (t0 (e13 u0) (e0 u0))
  let e15 (u0 : M) : Prop := (t2 (e7 u0) (e9 u0))
  let e16 (u0 : M) : Prop := (t0 (e15 u0) (e0 u0))
  let e17 (u0 : M) : Prop := (t0 (e7 u0) (e1))
  let e18 (u0 : M) : Prop := (t0 (e7 u0) (e3))
  let e19 (u0 : M) : Prop := (t0 (e5 u0) (e3))
  let e20 (u0 : M) : Prop := (t0 (a2 u0) (e19 u0))
  let e21 (u0 : M) : Prop := (t0 (e2) (a4 u0))
  let e22 (u0 : M) : Prop := (t0 (a2 u0) (e21 u0))
  have v0 : ((show Prop from (t3 (e1) (e3)))) := p391 (M := M) (fun w0 : M => (a3 w0))
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e5 x0_0))))) := p411 (M := M) (fun w0 : M => (a4 w0)) (h1)
  have v2 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e7 x0_0))))) := p413 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (e5 w0)) (h0) (v1)
  have v3 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p46 (e10 z0) (a3 z0) (a4 z0) (h2 z0)
  have v4 : (∀ z0 : M, (e14 z0)) := fun z0 : M => p83 (e10 z0) (e5 z0) (e0 z0) (v3 z0)
  have v5 : (∀ z0 : M, (e16 z0)) := fun z0 : M => p97 (a2 z0) (e9 z0) (e5 z0) (e0 z0) (v4 z0)
  have v6 : (∀ z0 : M, (e17 z0)) := fun z0 : M => p441 (M := M) (a1) (fun w0 : M => (e7 w0)) (fun w0 : M => (e0 w0)) (v2) ((fun w0 : M => v5 w0)) z0
  have v7 : (∀ z0 : M, (e18 z0)) := fun z0 : M => p153 (e7 z0) (e1) (e3) (v0) (v6 z0)
  have v8 : (∀ z0 : M, (e20 z0)) := fun z0 : M => p84 (a2 z0) (e5 z0) (e3) (v7 z0)
  have v9 : (∀ z0 : M, (e22 z0)) := fun z0 : M => p47 (a2 z0) (a4 z0) (e2) (v8 z0)
  exact v9
-- Actual MMB 447 ealieh
theorem p448 (a0 : Prop) (a2 : Prop) (a3 : M) (a4 : M → Prop) (h0 : (∀ z0 : M, (g487 (M := M) a0 a2 a3 a4 z0))) : (g488 (M := M) a0 a2 a3 a4 ) := by
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (a2))))) := p405 (M := M) (a2)
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (a0))))) := p405 (M := M) (a0)
  have v2 : ((show Prop from (t0 (a2) ((show Prop from (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (a4 x0_0))))) (a0))))))) := p446 (M := M) (a3) (fun w0 : M => (a2)) (fun w0 : M => (a4 w0)) (fun w0 : M => (a0)) (v0) (v1) ((fun w0 : M => h0 w0)) 0
  exact v2
-- Actual MMB 449 ealie
theorem p450 (a1 : Prop) (a2 : M → Prop)  : (g489 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t2 (a1) (a2 u0))
  let e1 (u0 : M) : Prop := (t0 (e0 u0) (a1))
  let e2  : Prop := (t9 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4 (u0 : M) : Prop := (t0 (e0 u0) (a2 u0))
  let e5  : Prop := (t9 (M := M) (fun x0_0 : M => (a2 x0_0)))
  let e7  : Prop := (t2 (a1) (e5))
  let e9 (u0 : M) : Prop := (t0 (a2 u0) (e0 u0))
  let e10 (u0 : M) : Prop := (t0 (a1) (e9 u0))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p53 _ _
  have v1 : ((show Prop from (t0 (e2) (a1)))) := p339 (M := M) (fun w0 : M => (e0 w0)) _ ((fun w0 : M => v0 w0))
  have v2 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p54 _ _
  have v3 : ((show Prop from (t0 (e2) (e5)))) := p377 (M := M) (fun w0 : M => (e0 w0)) (fun w0 : M => (a2 w0)) ((fun w0 : M => v2 w0))
  have v4 : ((show Prop from (t0 (e2) (e7)))) := p58 _ _ _ (v1) (v3)
  have v5 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p57 _ _
  have v6 : ((show Prop from (t0 (a1) ((show Prop from (t0 (e5) (e2))))))) := p398 (M := M) _ (fun w0 : M => (a2 w0)) (fun w0 : M => (e0 w0)) ((fun w0 : M => v5 w0))
  have v7 : ((show Prop from (t0 (e7) (e2)))) := p83 _ _ _ (v6)
  have v8 : ((show Prop from (t3 (e2) (e7)))) := p112 _ _ (v4) (v7)
  exact v8
-- Actual MMB 451 exan2
theorem p451 (a1 : M → Prop) (a2 : Prop)  : (g490 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t2 (a1 u0) (a2))
  let e1  : Prop := (t9 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e2 (u0 : M) : Prop := (t2 (a2) (a1 u0))
  let e3  : Prop := (t9 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e4  : Prop := (t9 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e5  : Prop := (t2 (e4) (a2))
  let e6  : Prop := (t3 (e1) (e3))
  let e7  : Prop := (t3 (e3) (e5))
  let e8  : Prop := (t3 (e1) (e5))
  let e9  : Prop := (t0 (e7) (e8))
  let e11 (u0 : M) : Prop := (t3 (e0 u0) (e2 u0))
  let e12  : Prop := (t2 (a2) (e4))
  let e13  : Prop := (t3 (e3) (e12))
  let e14  : Prop := (t3 (e12) (e5))
  let e15  : Prop := (t0 (e14) (e7))
  have v0 : ((show Prop from (t0 (e6) (e9)))) := p149 _ _ _
  have v1 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p177 _ _
  have v2 : (e6) := p380 (M := M) (fun w0 : M => (e0 w0)) (fun w0 : M => (e2 w0)) ((fun w0 : M => v1 w0))
  have v3 : (e9) := ((v0) (v2))
  have v4 : ((show Prop from (t0 (e13) (e15)))) := p149 _ _ _
  have v5 : (e13) := p450 (M := M) _ (fun w0 : M => (a1 w0))
  have v6 : (e15) := ((v4) (v5))
  have v7 : (e14) := p177 _ _
  have v8 : (e7) := ((v6) (v7))
  have v9 : (e8) := ((v3) (v8))
  exact v9
-- Actual MMB 452 bian1exi
theorem p480 (a2 : M → M → Prop) (a3 : M → M → Prop) (h0 : (∀ z0 : M, (g529 (M := M) a2 a3 z0))) (h1 : (∀ z0 : M, (g530 (M := M) a2 a3 z0))) (h2 : (∀ z0 : M, (∀ z1 : M, (g531 (M := M) a2 a3 z0 z1)))) : (∀ z0 : M, (∀ z1 : M, (g532 (M := M) a2 a3 z0 z1))) := by
  let e0 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (a2 x0_0 u0)))
  let e2 (u0 : M) (u1 : M) : Prop := (t0 (e0 u1) (a3 u0 u1))
  let e3 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (a3 u0 x0_0)))
  let e4 (u0 : M) (u1 : M) : Prop := (t0 (e0 u1) (e3 u0))
  let e6 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e7 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e8 (u0 : M) (u1 : M) : Prop := (t0 (e6 u0 u1) (e7 u0 u1))
  let e9 (u0 : M) (u1 : M) : Prop := (t3 (a2 u0 u1) (a3 u0 u1))
  let e10 (u0 : M) (u1 : M) : Prop := (t0 (e6 u0 u1) (e9 u0 u1))
  let e11 (u0 : M) (u1 : M) : Prop := (t3 (a3 u0 u1) (a2 u0 u1))
  let e12 (u0 : M) (u1 : M) : Prop := (t0 (e6 u0 u1) (e11 u0 u1))
  let e13 (u0 : M) (u1 : M) : Prop := (t0 (e3 u0) (a2 u0 u1))
  let e14 (u0 : M) (u1 : M) : Prop := (t0 (e3 u0) (e0 u1))
  let e15 (u0 : M) (u1 : M) : Prop := (t3 (e0 u1) (e3 u0))
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e0 x0_0))))) := p410 (M := M) (fun w0 : M => (fun w1 : M => (a2 w1 w0))) ((fun w1 : M => h0 w1))
  have v1 : (∀ z0 : M, (∀ z1 : M, (e2 z0 z1))) := fun z0 : M => fun z1 : M => p429 (M := M) z1 (fun w0 : M => (a2 w0 z1)) (fun w0 : M => (a3 w0 z1)) (h1 z1) ((fun w0 : M => h2 w0 z1)) z0
  have v2 : (∀ z0 : M, (∀ z1 : M, (e4 z0 z1))) := fun z0 : M => fun z1 : M => p419 (M := M) (fun w0 : M => (e0 w0)) (fun w0 : M => (a3 z0 w0)) (v0) ((fun w0 : M => v1 z0 w0)) z1
  have v3 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e3 x0_0))))) := p410 (M := M) (fun w0 : M => (fun w1 : M => (a3 w0 w1))) ((fun w1 : M => h1 w1))
  have v4 : (∀ z0 : M, (∀ z1 : M, (e8 z0 z1))) := fun z0 : M => fun z1 : M => p341 (M := M) z1 z0
  have v5 : (∀ z0 : M, (∀ z1 : M, (e10 z0 z1))) := fun z0 : M => fun z1 : M => p10 (e6 z0 z1) (e7 z0 z1) (e9 z0 z1) (h2 z0 z1) (v4 z0 z1)
  have v6 : (∀ z0 : M, (∀ z1 : M, (e12 z0 z1))) := fun z0 : M => fun z1 : M => p144 (e6 z0 z1) (a2 z0 z1) (a3 z0 z1) (v5 z0 z1)
  have v7 : (∀ z0 : M, (∀ z1 : M, (e13 z0 z1))) := fun z0 : M => fun z1 : M => p429 (M := M) z0 (fun w0 : M => (a3 z0 w0)) (fun w0 : M => (a2 z0 w0)) (h0 z0) ((fun w0 : M => v6 z0 w0)) z1
  have v8 : (∀ z0 : M, (∀ z1 : M, (e14 z0 z1))) := fun z0 : M => fun z1 : M => p419 (M := M) (fun w0 : M => (e3 w0)) (fun w0 : M => (a2 w0 z1)) (v3) ((fun w0 : M => v7 w0 z1)) z0
  have v9 : (∀ z0 : M, (∀ z1 : M, (e15 z0 z1))) := fun z0 : M => fun z1 : M => p112 (e0 z1) (e3 z0) (v2 z0 z1) (v8 z0 z1)
  exact v9
-- Actual MMB 481 cbval
theorem p481 (a2 : M → Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (∀ z1 : M, (g533 (M := M) a2 a3 z0 z1)))) : (g534 (M := M) a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a2 u0)))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a3 u0)))
  have v0 : (∀ z0 : M, (e0 z0)) := fun z0 : M => p405 (M := M) (a2 z0)
  have v1 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p405 (M := M) (a3 z0)
  have v2 : ((show Prop from (t3 ((show Prop from (t8 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (a3 x0_0)))))))) := p480 (M := M) (fun w0 : M => (fun w1 : M => (a2 w0))) (fun w0 : M => (fun w1 : M => (a3 w1))) ((fun w0 : M => v0 w0)) ((fun w1 : M => v1 w1)) ((fun w0 : M => (fun w1 : M => h0 w0 w1))) 0 0
  exact v2
-- Actual MMB 482 cbvexh
theorem p482 (a2 : M → M → Prop) (a3 : M → M → Prop) (h0 : (∀ z0 : M, (g529 (M := M) a2 a3 z0))) (h1 : (∀ z0 : M, (g530 (M := M) a2 a3 z0))) (h2 : (∀ z0 : M, (∀ z1 : M, (g531 (M := M) a2 a3 z0 z1)))) : (∀ z0 : M, (∀ z1 : M, (g535 (M := M) a2 a3 z0 z1))) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t1 (a2 u0 u1))
  let e1 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0 u0)))
  let e2 (u0 : M) (u1 : M) : Prop := (t1 (a3 u0 u1))
  let e3 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e2 u0 x0_0)))
  let e4 (u0 : M) (u1 : M) : Prop := (t3 (e1 u1) (e3 u0))
  let e5 (u0 : M) : Prop := (t1 (e1 u0))
  let e6 (u0 : M) : Prop := (t1 (e3 u0))
  let e7 (u0 : M) (u1 : M) : Prop := (t3 (e5 u1) (e6 u0))
  let e8 (u0 : M) (u1 : M) : Prop := (t0 (e4 u0 u1) (e7 u0 u1))
  let e9 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (a2 x0_0 u0)))
  let e10 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (a3 u0 x0_0)))
  let e11 (u0 : M) (u1 : M) : Prop := (t3 (e9 u1) (e10 u0))
  let e12 (u0 : M) (u1 : M) : Prop := (t0 (e4 u0 u1) (e11 u0 u1))
  let e13 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0 x0_0)))
  let e14 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 x0_0 u0)))
  let e15 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e16 (u0 : M) (u1 : M) : Prop := (t3 (e0 u0 u1) (e2 u0 u1))
  let e17 (u0 : M) (u1 : M) : Prop := (t0 (e15 u0 u1) (e16 u0 u1))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e8 z0 z1))) := fun z0 : M => fun z1 : M => p185 (e1 z1) (e3 z0)
  have v1 : (∀ z0 : M, (∀ z1 : M, (e12 z0 z1))) := (show (∀ z0 : M, (∀ z1 : M, (e12 z0 z1))) from v0)
  have v2 : (∀ z0 : M, (e13 z0)) := fun z0 : M => p411 (M := M) (fun w0 : M => (a2 z0 w0)) (h0 z0)
  have v3 : (∀ z0 : M, (e14 z0)) := fun z0 : M => p411 (M := M) (fun w0 : M => (a3 w0 z0)) (h1 z0)
  have v4 : (∀ z0 : M, (∀ z1 : M, (e17 z0 z1))) := fun z0 : M => fun z1 : M => p187 (e15 z0 z1) (a2 z0 z1) (a3 z0 z1) (h2 z0 z1)
  have v5 : (∀ z0 : M, (∀ z1 : M, (e4 z0 z1))) := fun z0 : M => fun z1 : M => p480 (M := M) (fun w0 : M => (fun w1 : M => (e0 w0 w1))) (fun w0 : M => (fun w1 : M => (e2 w0 w1))) ((fun w0 : M => v2 w0)) ((fun w1 : M => v3 w1)) ((fun w0 : M => (fun w1 : M => v4 w0 w1))) z0 z1
  have v6 : (∀ z0 : M, (∀ z1 : M, (e11 z0 z1))) := fun z0 : M => fun z1 : M => b3 (e4 z0 z1) (e11 z0 z1) (v1 z0 z1) (v5 z0 z1)
  exact v6
-- Actual MMB 483 cbvex
theorem p483 (a2 : M → Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (∀ z1 : M, (g533 (M := M) a2 a3 z0 z1)))) : (g536 (M := M) a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a2 u0)))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a3 u0)))
  have v0 : (∀ z0 : M, (e0 z0)) := fun z0 : M => p405 (M := M) (a2 z0)
  have v1 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p405 (M := M) (a3 z0)
  have v2 : ((show Prop from (t3 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show Prop from (t9 (M := M) (fun x0_0 : M => (a3 x0_0)))))))) := p482 (M := M) (fun w0 : M => (fun w1 : M => (a2 w0))) (fun w0 : M => (fun w1 : M => (a3 w1))) ((fun w0 : M => v0 w0)) ((fun w1 : M => v1 w1)) ((fun w0 : M => (fun w1 : M => h0 w0 w1))) 0 0
  exact v2
-- Actual MMB 484 pimex
theorem p509 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M) (h0 : (g354 (M := M) a0 a1 a2 a3 a4 )) (h1 : (g355 (M := M) a0 a1 a2 a3 a4 )) : (g576 (M := M) a0 a1 a2 a3 a4 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a3))
  let e1  : Prop := (t10 (M := M) (a2) (a4))
  let e11  : Prop := (t0 (a0) ((show Prop from (t3 ((show Prop from (t13 (M := M) (a1) (a3)))) ((show Prop from (t13 (M := M) (a2) (a4))))))))
  have v0 : ((show Prop from (t0 (a0) ((show Prop from (t3 (e0) (e1))))))) := p350 (M := M) _ (a1) (a2) (a3) (a4) (h0) (h1)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t3 ((show Prop from (t1 (e0)))) ((show Prop from (t1 (e1)))))))))) := p187 _ _ _ (v0)
  have v2 : (e11) := (show (e11) from v1)
  exact v2
-- Actual MMB 510 neeq
theorem p511 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (g350 (M := M) a0 a1 a2 a3 )) : (g578 (M := M) a0 a1 a2 a3 ) := by
  have v0 : ((show Prop from (t0 (a0) ((show Prop from (t10 (M := M) (a3) (a3))))))) := p354 (M := M) (a0) (a3)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t3 ((show Prop from (t13 (M := M) (a1) (a3)))) ((show Prop from (t13 (M := M) (a2) (a3)))))))))) := p509 (M := M) (a0) (a1) (a2) (a3) (a3) (h0) (v0)
  exact v1
-- Actual MMB 512 neeq1
theorem p512 (a0 : M) (a1 : M) (a2 : M)  : (g579 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t10 (M := M) (a0) (a1))
  have v0 : ((show Prop from (t0 (e0) (e0)))) := p8 (e0)
  have v1 : ((show Prop from (t0 (e0) ((show Prop from (t3 ((show Prop from (t13 (M := M) (a0) (a2)))) ((show Prop from (t13 (M := M) (a1) (a2)))))))))) := p511 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 513 neeq2d
theorem p515 (a0 : M) (a1 : M)  : (g582 (M := M) a0 a1 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a0))
  let e1  : Prop := (t10 (M := M) (a0) (a1))
  let e2  : Prop := (t0 (e0) (e1))
  let e9  : Prop := (t0 ((show Prop from (t13 (M := M) (a0) (a1)))) ((show Prop from (t13 (M := M) (a1) (a0)))))
  let e10  : Prop := (t0 (e2) (e9))
  have v0 : ((show Prop from (t0 (e2) ((show Prop from (t0 ((show Prop from (t1 (e1)))) ((show Prop from (t1 (e0)))))))))) := p40 _ _
  have v1 : (e10) := (show (e10) from v0)
  have v2 : (e2) := p341 (M := M) (a1) (a0)
  have v3 : (e9) := ((v1) (v2))
  exact v3
-- Actual MMB 516 sbq
theorem p516 (a1 : M) (a2 : M → Prop)  : (∀ z0 : M, (g583 (M := M) a1 a2 z0)) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e1 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (a2 u1))
  let e2 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e1 u0 x0_0)))
  let e3 (u0 : M) (u1 : M) : Prop := (t0 (a2 u1) (e2 u0))
  let e4 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e3 u0 u1))
  let e5 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e6 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e7 (u0 : M) : Prop := (t2 (e5 u0) (a2 u0))
  let e8 (u0 : M) (u1 : M) : Prop := (t2 (e7 u1) (e6 u0))
  let e9 (u0 : M) (u1 : M) : Prop := (t0 (e8 u0 u1) (e5 u1))
  let e10 (u0 : M) (u1 : M) : Prop := (t0 (e8 u0 u1) (e6 u0))
  let e11 (u0 : M) (u1 : M) : Prop := (t0 (e8 u0 u1) (e0 u0 u1))
  let e12 (u0 : M) (u1 : M) : Prop := (t0 (e8 u0 u1) (a2 u1))
  let e13 (u0 : M) (u1 : M) : Prop := (t0 (e8 u0 u1) (e2 u0))
  let e14 (u0 : M) : Prop := (t0 (e6 u0) (e2 u0))
  let e15  : Prop := (t8 (M := M) (fun x0_0 : M => (e14 x0_0)))
  let e16 (u0 : M) : Prop := (t0 (e7 u0) (e15))
  let e17 (u0 : M) : Prop := (t0 (a2 u0) (e15))
  let e18 (u0 : M) : Prop := (t0 (e5 u0) (e17 u0))
  let e19  : Prop := (t9 (M := M) (fun x0_0 : M => (e6 x0_0)))
  let e20 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e5 u0)))
  let e22 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a2 u0)))
  let e23 (u0 : M) : Prop := (t0 (e15) (a2 u0))
  let e24 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e23 u0)))
  let e25 (u0 : M) : Prop := (t0 (e15) (e14 u0))
  let e26 (u0 : M) (u1 : M) : Prop := (t2 (e5 u1) (e6 u0))
  let e27 (u0 : M) (u1 : M) : Prop := (t0 (e26 u0 u1) (e6 u0))
  let e28 (u0 : M) (u1 : M) : Prop := (t0 (e26 u0 u1) (e2 u0))
  let e29 (u0 : M) (u1 : M) : Prop := (t0 (e14 u0) (e28 u0 u1))
  let e30 (u0 : M) : Prop := (t0 (e14 u0) (e2 u0))
  let e31 (u0 : M) (u1 : M) : Prop := (t0 (e26 u0 u1) (e30 u0))
  let e32 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0) (e1 u0 u1))
  let e33 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0) (a2 u1))
  let e34 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e33 u0 u1))
  let e35 (u0 : M) (u1 : M) : Prop := (t0 (e6 u0) (e0 u0 u1))
  let e36 (u0 : M) (u1 : M) : Prop := (t0 (e5 u1) (e35 u0 u1))
  let e37 (u0 : M) (u1 : M) : Prop := (t0 (e26 u0 u1) (e0 u0 u1))
  let e38 (u0 : M) (u1 : M) : Prop := (t0 (e26 u0 u1) (e33 u0 u1))
  let e39 (u0 : M) (u1 : M) : Prop := (t0 (e14 u0) (a2 u1))
  let e40 (u0 : M) (u1 : M) : Prop := (t0 (e26 u0 u1) (e39 u0 u1))
  let e41 (u0 : M) (u1 : M) : Prop := (t0 (e26 u0 u1) (e23 u1))
  let e42 (u0 : M) (u1 : M) : Prop := (t0 (e6 u0) (e23 u1))
  let e43 (u0 : M) (u1 : M) : Prop := (t0 (e5 u1) (e42 u0 u1))
  let e44 (u0 : M) : Prop := (t0 (e19) (e23 u0))
  let e45 (u0 : M) : Prop := (t0 (e5 u0) (e44 u0))
  let e46 (u0 : M) : Prop := (t0 (e5 u0) (e23 u0))
  let e47 (u0 : M) : Prop := (t3 (a2 u0) (e15))
  let e48 (u0 : M) : Prop := (t0 (e5 u0) (e47 u0))
  let e50 (u0 : M) : Prop := (t3 (a2 u0) ((show Prop from (t14 (M := M) (a1) (fun x0_1 : M => (a2 x0_1))))))
  let e51 (u0 : M) : Prop := (t0 (e5 u0) (e50 u0))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e4 z0 z1))) := fun z0 : M => fun z1 : M => b336 (M := M) z0 (fun w0 : M => (a2 w0)) z1
  have v1 : (∀ z0 : M, (∀ z1 : M, (e9 z0 z1))) := fun z0 : M => fun z1 : M => p64 (e5 z1) (a2 z1) (e6 z0)
  have v2 : (∀ z0 : M, (∀ z1 : M, (e10 z0 z1))) := fun z0 : M => fun z1 : M => p54 (e7 z1) (e6 z0)
  have v3 : (∀ z0 : M, (∀ z1 : M, (e11 z0 z1))) := fun z0 : M => fun z1 : M => p359 (M := M) (e8 z0 z1) z1 (a1) z0 (v1 z0 z1) (v2 z0 z1)
  have v4 : (∀ z0 : M, (∀ z1 : M, (e12 z0 z1))) := fun z0 : M => fun z1 : M => p65 (e5 z1) (a2 z1) (e6 z0)
  have v5 : (∀ z0 : M, (∀ z1 : M, (e13 z0 z1))) := fun z0 : M => fun z1 : M => p15 (e8 z0 z1) (e0 z0 z1) (a2 z1) (e2 z0) (v0 z0 z1) (v3 z0 z1) (v4 z0 z1)
  have v6 : (∀ z0 : M, (e16 z0)) := fun z0 : M => p372 (M := M) (e7 z0) (fun w0 : M => (e6 w0)) (fun w0 : M => (e2 w0)) ((fun w0 : M => v5 w0 z0))
  have v7 : (∀ z0 : M, (e18 z0)) := fun z0 : M => p84 (e5 z0) (a2 z0) (e15) (v6 z0)
  have v8 : (e19) := b330 (M := M) (a1)
  have v9 : (∀ z0 : M, (e20 z0)) := fun z0 : M => p405 (M := M) (e5 z0)
  have v10 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e15))))) := p418 (M := M) (fun w0 : M => (e14 w0))
  have v11 : (∀ z0 : M, (e22 z0)) := fun z0 : M => p405 (M := M) (a2 z0)
  have v12 : (∀ z0 : M, (e24 z0)) := fun z0 : M => p412 (M := M) (fun w0 : M => (e15)) (fun w0 : M => (a2 z0)) (v10) (v11 z0)
  have v13 : (∀ z0 : M, (e25 z0)) := fun z0 : M => p392 (M := M) (fun w0 : M => (e14 w0)) z0
  have v14 : (∀ z0 : M, (∀ z1 : M, (e27 z0 z1))) := fun z0 : M => fun z1 : M => p54 (e5 z1) (e6 z0)
  have v15 : (∀ z0 : M, (∀ z1 : M, (e29 z0 z1))) := fun z0 : M => fun z1 : M => p29 (e26 z0 z1) (e6 z0) (e2 z0) (v14 z0 z1)
  have v16 : (∀ z0 : M, (∀ z1 : M, (e31 z0 z1))) := fun z0 : M => fun z1 : M => p23 (e14 z0) (e26 z0 z1) (e2 z0) (v15 z0 z1)
  have v17 : (∀ z0 : M, (∀ z1 : M, (e32 z0 z1))) := fun z0 : M => fun z1 : M => p392 (M := M) (fun w0 : M => (e1 z0 w0)) z1
  have v18 : (∀ z0 : M, (∀ z1 : M, (e34 z0 z1))) := fun z0 : M => fun z1 : M => p23 (e2 z0) (e0 z0 z1) (a2 z1) (v17 z0 z1)
  have v19 : (∀ z0 : M, (∀ z1 : M, (e36 z0 z1))) := fun z0 : M => fun z1 : M => p344 (M := M) z1 (a1) z0
  have v20 : (∀ z0 : M, (∀ z1 : M, (e37 z0 z1))) := fun z0 : M => fun z1 : M => p83 (e5 z1) (e6 z0) (e0 z0 z1) (v19 z0 z1)
  have v21 : (∀ z0 : M, (∀ z1 : M, (e38 z0 z1))) := fun z0 : M => fun z1 : M => p10 (e26 z0 z1) (e0 z0 z1) (e33 z0 z1) (v18 z0 z1) (v20 z0 z1)
  have v22 : (∀ z0 : M, (∀ z1 : M, (e40 z0 z1))) := fun z0 : M => fun z1 : M => p16 (e26 z0 z1) (e14 z0) (e2 z0) (a2 z1) (v16 z0 z1) (v21 z0 z1)
  have v23 : (∀ z0 : M, (∀ z1 : M, (e41 z0 z1))) := fun z0 : M => fun z1 : M => p17 (e26 z0 z1) (e15) (e14 z0) (a2 z1) (v13 z0) (v22 z0 z1)
  have v24 : (∀ z0 : M, (∀ z1 : M, (e43 z0 z1))) := fun z0 : M => fun z1 : M => p84 (e5 z1) (e6 z0) (e23 z1) (v23 z0 z1)
  have v25 : (∀ z0 : M, (e45 z0)) := fun z0 : M => p421 (M := M) (fun w0 : M => (e5 z0)) (fun w0 : M => (e6 w0)) (fun w0 : M => (e23 z0)) (v9 z0) (v12 z0) ((fun w0 : M => v24 w0 z0)) 0
  have v26 : (∀ z0 : M, (e46 z0)) := fun z0 : M => p7 (e5 z0) (e19) (e23 z0) (v8) (v25 z0)
  have v27 : (∀ z0 : M, (e48 z0)) := fun z0 : M => p113 (e5 z0) (a2 z0) (e15) (v7 z0) (v26 z0)
  have v28 : (∀ z0 : M, (e51 z0)) := (show (∀ z0 : M, (e51 z0)) from v27)
  exact v28
-- Actual MMB 517 sbqcom
theorem p518 (a1 : M) (a2 : M → Prop)  : (g585 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0)))
  let e2 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e3 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0 u1) (a2 u1))
  let e4 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e3 u0 x0_0)))
  let e5 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e4 u0)))
  let e6 (u0 : M) : Prop := (t0 (e0 u0) (e4 u0))
  let e7 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e6 u0)))
  let e11  : Prop := (t11 (M := M) (fun x0_0 : M => ((show Prop from (t14 (M := M) (a1) (fun x0_1 : M => (a2 x0_1)))))))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p405 (M := M) (e0 z0)
  have v1 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p418 (M := M) (fun w0 : M => (e3 z0 w0))
  have v2 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p412 (M := M) (fun w0 : M => (e0 z0)) (fun w0 : M => (e4 z0)) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t11 (M := M) (fun x0_0 : M => ((show Prop from (t8 (M := M) (fun x0_0 : M => (e6 x0_0))))))))) := p410 (M := M) (fun w0 : M => (fun w1 : M => (e6 w1))) ((fun w1 : M => v2 w1))
  have v4 : (e11) := (show (e11) from v3)
  exact v4
-- Actual MMB 519 nfsb
theorem p519 (a2 : M → M) (a3 : M → M → Prop) (h0 : (∀ z0 : M, (g586 (M := M) a2 a3 z0))) : (∀ z0 : M, (g587 (M := M) a2 a3 z0)) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a2 u1))
  let e1 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0 u1)))
  let e2 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e3 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0 u1)))
  let e4 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e2 u0 u2) (a3 u1 u2))
  let e5 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e4 u0 x0_0 u1)))
  let e6 (u0 : M) (u1 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e4 u0 u1 x0_0)))
  let e7 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e6 u0 x0_0)))
  let e8 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e0 u0 u2) (e6 u0 u1))
  let e9 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e8 u0 x0_0 u1)))
  let e10 (u0 : M) (u1 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e8 x0_0 u0 u1)))
  let e11 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e10 x0_0 u0)))
  let e12 (u0 : M) (u1 : M) : Prop := (t14 (M := M) (a2 u1) (fun x0_1 : M => (a3 u0 x0_1)))
  let e13 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e12 x0_0 u0)))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e1 z0 z1))) := fun z0 : M => fun z1 : M => p405 (M := M) (e0 z0 z1)
  have v1 : (∀ z0 : M, (∀ z1 : M, (e3 z0 z1))) := fun z0 : M => fun z1 : M => p405 (M := M) (e2 z0 z1)
  have v2 : (∀ z0 : M, (∀ z1 : M, (e5 z0 z1))) := fun z0 : M => fun z1 : M => p412 (M := M) (fun w0 : M => (e2 z0 z1)) (fun w0 : M => (a3 w0 z1)) (v1 z0 z1) (h0 z1)
  have v3 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p410 (M := M) (fun w0 : M => (fun w1 : M => (e4 z0 w0 w1))) ((fun w1 : M => v2 z0 w1))
  have v4 : (∀ z0 : M, (∀ z1 : M, (e9 z0 z1))) := fun z0 : M => fun z1 : M => p412 (M := M) (fun w0 : M => (e0 z0 z1)) (fun w0 : M => (e6 z0 w0)) (v0 z0 z1) (v3 z0)
  have v5 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p410 (M := M) (fun w0 : M => (fun w1 : M => (e8 w1 w0 z0))) ((fun w1 : M => v4 w1 z0))
  have v6 : (∀ z0 : M, (e13 z0)) := (show (∀ z0 : M, (e13 z0)) from v5)
  exact v6
-- Actual MMB 520 sbeq1
theorem p520 (a1 : M → M) (a2 : M → M) (a3 : M → Prop)  : (∀ z0 : M, (g588 (M := M) a1 a2 a3 z0)) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) (a1 u0) (a2 u0))
  let e1 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a1 u1))
  let e2 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a2 u1))
  let e3 (u0 : M) (u1 : M) : Prop := (t3 (e1 u0 u1) (e2 u0 u1))
  let e4 (u0 : M) (u1 : M) : Prop := (t0 (e0 u1) (e3 u0 u1))
  let e5 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e6 (u0 : M) (u1 : M) : Prop := (t0 (e5 u0 u1) (a3 u1))
  let e7 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e6 u0 x0_0)))
  let e8 (u0 : M) (u1 : M) : Prop := (t0 (e1 u0 u1) (e7 u0))
  let e9 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0 u1) (e7 u0))
  let e10 (u0 : M) (u1 : M) : Prop := (t3 (e8 u0 u1) (e9 u0 u1))
  let e11 (u0 : M) (u1 : M) : Prop := (t0 (e0 u1) (e10 u0 u1))
  let e12 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e8 x0_0 u0)))
  let e13 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e9 x0_0 u0)))
  let e14 (u0 : M) : Prop := (t3 (e12 u0) (e13 u0))
  let e15 (u0 : M) : Prop := (t0 (e0 u0) (e14 u0))
  let e16 (u0 : M) : Prop := (t14 (M := M) (a1 u0) (fun x0_1 : M => (a3 x0_1)))
  let e17 (u0 : M) : Prop := (t14 (M := M) (a2 u0) (fun x0_1 : M => (a3 x0_1)))
  let e18 (u0 : M) : Prop := (t3 (e16 u0) (e17 u0))
  let e19 (u0 : M) : Prop := (t0 (e0 u0) (e18 u0))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e4 z0 z1))) := fun z0 : M => fun z1 : M => p347 (M := M) z0 (a1 z1) (a2 z1)
  have v1 : (∀ z0 : M, (∀ z1 : M, (e11 z0 z1))) := fun z0 : M => fun z1 : M => p191 (e0 z1) (e1 z0 z1) (e2 z0 z1) (e7 z0) (v0 z0 z1)
  have v2 : (∀ z0 : M, (e15 z0)) := fun z0 : M => p371 (M := M) (e0 z0) (fun w1 : M => (e8 w1 z0)) (fun w1 : M => (e9 w1 z0)) ((fun w1 : M => v1 w1 z0))
  have v3 : (∀ z0 : M, (e19 z0)) := (show (∀ z0 : M, (e19 z0)) from v2)
  exact v3
-- Actual MMB 521 sbeq1d
theorem p521 (a1 : M → Prop) (a2 : M → M) (a3 : M → M) (a4 : M → Prop) (h0 : (∀ z0 : M, (g589 (M := M) a1 a2 a3 a4 z0))) : (∀ z0 : M, (g590 (M := M) a1 a2 a3 a4 z0)) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) (a2 u0) (a3 u0))
  let e1 (u0 : M) : Prop := (t14 (M := M) (a2 u0) (fun x0_1 : M => (a4 x0_1)))
  let e2 (u0 : M) : Prop := (t14 (M := M) (a3 u0) (fun x0_1 : M => (a4 x0_1)))
  let e3 (u0 : M) : Prop := (t3 (e1 u0) (e2 u0))
  let e4 (u0 : M) : Prop := (t0 (e0 u0) (e3 u0))
  let e5 (u0 : M) : Prop := (t0 (a1 u0) (e3 u0))
  have v0 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p520 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3 w0)) (fun w0 : M => (a4 w0)) z0
  have v1 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p10 (a1 z0) (e0 z0) (e3 z0) (v0 z0) (h0 z0)
  exact v1
-- Actual MMB 522 sbeqd
theorem p522 (a0 : Prop) (a2 : M → M) (a3 : M → M) (a4 : M → Prop) (a5 : M → Prop) (h0 : (∀ z0 : M, (g591 (M := M) a0 a2 a3 a4 a5 z0))) (h1 : (∀ z0 : M, (g592 (M := M) a0 a2 a3 a4 a5 z0))) : (∀ z0 : M, (g593 (M := M) a0 a2 a3 a4 a5 z0)) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a2 u1))
  let e1 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a3 u1))
  let e2 (u0 : M) (u1 : M) : Prop := (t3 (e0 u0 u1) (e1 u0 u1))
  let e3 (u0 : M) (u1 : M) : Prop := (t0 (a0) (e2 u0 u1))
  let e4 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e5 (u0 : M) (u1 : M) : Prop := (t0 (e4 u0 u1) (a4 u1))
  let e6 (u0 : M) (u1 : M) : Prop := (t0 (e4 u0 u1) (a5 u1))
  let e7 (u0 : M) (u1 : M) : Prop := (t3 (e5 u0 u1) (e6 u0 u1))
  let e8 (u0 : M) (u1 : M) : Prop := (t0 (a0) (e7 u0 u1))
  let e9 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e5 u0 x0_0)))
  let e10 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e6 u0 x0_0)))
  let e11 (u0 : M) : Prop := (t3 (e9 u0) (e10 u0))
  let e12 (u0 : M) : Prop := (t0 (a0) (e11 u0))
  let e13 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e9 u0))
  let e14 (u0 : M) (u1 : M) : Prop := (t0 (e1 u0 u1) (e10 u0))
  let e15 (u0 : M) (u1 : M) : Prop := (t3 (e13 u0 u1) (e14 u0 u1))
  let e16 (u0 : M) (u1 : M) : Prop := (t0 (a0) (e15 u0 u1))
  let e17 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e13 x0_0 u0)))
  let e18 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e14 x0_0 u0)))
  let e19 (u0 : M) : Prop := (t3 (e17 u0) (e18 u0))
  let e20 (u0 : M) : Prop := (t0 (a0) (e19 u0))
  let e21 (u0 : M) : Prop := (t14 (M := M) (a2 u0) (fun x0_1 : M => (a4 x0_1)))
  let e22 (u0 : M) : Prop := (t14 (M := M) (a3 u0) (fun x0_1 : M => (a5 x0_1)))
  let e23 (u0 : M) : Prop := (t3 (e21 u0) (e22 u0))
  let e24 (u0 : M) : Prop := (t0 (a0) (e23 u0))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e3 z0 z1))) := fun z0 : M => fun z1 : M => p349 (M := M) (a0) z0 (a2 z1) (a3 z1) (h0 z1)
  have v1 : (∀ z0 : M, (∀ z1 : M, (e8 z0 z1))) := fun z0 : M => fun z1 : M => p192 (a0) (e4 z0 z1) (a4 z1) (a5 z1) (h1 z1)
  have v2 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p371 (M := M) (a0) (fun w1 : M => (e5 z0 w1)) (fun w1 : M => (e6 z0 w1)) ((fun w1 : M => v1 z0 w1))
  have v3 : (∀ z0 : M, (∀ z1 : M, (e16 z0 z1))) := fun z0 : M => fun z1 : M => p188 (a0) (e0 z0 z1) (e1 z0 z1) (e9 z0) (e10 z0) (v0 z0 z1) (v2 z0)
  have v4 : (∀ z0 : M, (e20 z0)) := fun z0 : M => p371 (M := M) (a0) (fun w1 : M => (e13 w1 z0)) (fun w1 : M => (e14 w1 z0)) ((fun w1 : M => v3 w1 z0))
  have v5 : (∀ z0 : M, (e24 z0)) := (show (∀ z0 : M, (e24 z0)) from v4)
  exact v5
-- Actual MMB 523 sbeq2d
theorem p523 (a0 : Prop) (a2 : M → M) (a3 : M → Prop) (a4 : M → Prop) (h0 : (∀ z0 : M, (g594 (M := M) a0 a2 a3 a4 z0))) : (∀ z0 : M, (g595 (M := M) a0 a2 a3 a4 z0)) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) (a2 u0) (a2 u0))
  let e1 (u0 : M) : Prop := (t0 (a0) (e0 u0))
  let e2 (u0 : M) : Prop := (t14 (M := M) (a2 u0) (fun x0_1 : M => (a3 x0_1)))
  let e3 (u0 : M) : Prop := (t14 (M := M) (a2 u0) (fun x0_1 : M => (a4 x0_1)))
  let e4 (u0 : M) : Prop := (t3 (e2 u0) (e3 u0))
  let e5 (u0 : M) : Prop := (t0 (a0) (e4 u0))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p354 (M := M) (a0) (a2 z0)
  have v1 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p522 (M := M) (a0) (fun w1 : M => (a2 w1)) (fun w1 : M => (a2 w1)) (fun w1 : M => (a3 w1)) (fun w1 : M => (a4 w1)) ((fun w1 : M => v0 w1)) ((fun w1 : M => h0 w1)) z0
  exact v1
-- Actual MMB 524 sbeq2i
theorem p525 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (h0 : (g453 (M := M) a1 a2 a3 )) : (∀ z0 : M, (g598 (M := M) a1 a2 a3 z0)) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t3 (a2 u0) (a3 u0))
  let e2 (u0 : M) : Prop := (t0 (e0 u0) (e1 u0))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e5  : Prop := (t14 (M := M) (a1) (fun x0_1 : M => (a2 x0_1)))
  let e7 (u0 : M) : Prop := (t3 (e5) (a3 u0))
  let e9 (u0 : M) : Prop := (t0 (e3) (e7 u0))
  let e11 (u0 : M) : Prop := (t3 (a2 u0) (e5))
  let e12 (u0 : M) : Prop := (t0 (e0 u0) (e11 u0))
  let e13 (u0 : M) : Prop := (t2 (e0 u0) (e3))
  let e14 (u0 : M) : Prop := (t0 (e13 u0) (e11 u0))
  let e15 (u0 : M) : Prop := (t0 (e3) (e2 u0))
  let e16 (u0 : M) : Prop := (t0 (e13 u0) (e1 u0))
  let e17 (u0 : M) : Prop := (t0 (e13 u0) (e7 u0))
  let e18 (u0 : M) : Prop := (t0 (e0 u0) (e9 u0))
  let e19  : Prop := (t9 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e20 (u0 : M) : Prop := (t0 (e19) (e9 u0))
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e3))))) := p418 (M := M) (fun w0 : M => (e2 w0))
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e5))))) := p518 (M := M) (a1) (fun w0 : M => (a2 w0))
  have v2 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e7 x0_0))))) := p415 (M := M) (fun w0 : M => (e5)) (fun w0 : M => (a3 w0)) (v1) (h0)
  have v3 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e9 x0_0))))) := p412 (M := M) (fun w0 : M => (e3)) (fun w0 : M => (e7 w0)) (v0) (v2)
  have v4 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p516 (M := M) (a1) (fun w0 : M => (a2 w0)) z0
  have v5 : (∀ z0 : M, (e14 z0)) := fun z0 : M => p62 (e0 z0) (e3) (e11 z0) (v4 z0)
  have v6 : (∀ z0 : M, (e15 z0)) := fun z0 : M => p392 (M := M) (fun w0 : M => (e2 w0)) z0
  have v7 : (∀ z0 : M, (e16 z0)) := fun z0 : M => p85 (e3) (e0 z0) (e1 z0) (v6 z0)
  have v8 : (∀ z0 : M, (e17 z0)) := fun z0 : M => p147 (e13 z0) (e5) (a2 z0) (a3 z0) (v5 z0) (v7 z0)
  have v9 : (∀ z0 : M, (e18 z0)) := fun z0 : M => p84 (e0 z0) (e3) (e7 z0) (v8 z0)
  have v10 : (∀ z0 : M, (e20 z0)) := fun z0 : M => p420 (M := M) (fun w0 : M => (e0 w0)) (fun w0 : M => (e9 w0)) (v3) ((fun w0 : M => v9 w0)) z0
  have v11 : (e19) := b330 (M := M) (a1)
  have v12 : (∀ z0 : M, (e9 z0)) := fun z0 : M => b3 (e19) (e9 z0) (v10 z0) (v11)
  exact v12
-- Actual MMB 526 sbeh
theorem p526 (a1 : M) (a2 : M → Prop) (a3 : M → Prop) (h0 : (g453 (M := M) a1 a2 a3 )) (h1 : (∀ z0 : M, (g454 (M := M) a1 a2 a3 z0))) : (∀ z0 : M, (g599 (M := M) a1 a2 a3 z0)) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t3 (a2 u0) (a3 u0))
  let e2 (u0 : M) : Prop := (t0 (e0 u0) (e1 u0))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e5 (u0 : M) : Prop := (t3 ((show Prop from (t14 (M := M) (a1) (fun x0_1 : M => (a2 x0_1))))) (a3 u0))
  let e6 (u0 : M) : Prop := (t0 (e3) (e5 u0))
  have v0 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p525 (M := M) (a1) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3 w0)) (h0) z0
  have v1 : (e3) := b325 (M := M) (fun w0 : M => (e2 w0)) ((fun w0 : M => h1 w0))
  have v2 : (∀ z0 : M, (e5 z0)) := fun z0 : M => b3 (e3) (e5 z0) (v0 z0) (v1)
  exact v2
-- Actual MMB 527 sbet
theorem p527 (a1 : M) (a2 : M → Prop) (a3 : Prop)  : (g600 (M := M) a1 a2 a3 ) := by
  let e1 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e2 (u0 : M) : Prop := (t3 (a2 u0) (a3))
  let e3 (u0 : M) : Prop := (t0 (e1 u0) (e2 u0))
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (a3))))) := p405 (M := M) (a3)
  have v1 : ((show Prop from (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e3 x0_0))))) ((show Prop from (t3 ((show Prop from (t14 (M := M) (a1) (fun x0_1 : M => (a2 x0_1))))) (a3))))))) := p525 (M := M) (a1) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3)) (v0) 0
  exact v1
-- Actual MMB 528 sbe
theorem p528 (a1 : M) (a2 : M → Prop) (a3 : Prop) (h0 : (∀ z0 : M, (g468 (M := M) a1 a2 a3 z0))) : (g601 (M := M) a1 a2 a3 ) := by
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (a3))))) := p405 (M := M) (a3)
  have v1 : ((show Prop from (t3 ((show Prop from (t14 (M := M) (a1) (fun x0_1 : M => (a2 x0_1))))) (a3)))) := p526 (M := M) (a1) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3)) (v0) ((fun w0 : M => h0 w0)) 0
  exact v1
-- Actual MMB 529 sbed
theorem p529 (a0 : Prop) (a2 : M) (a3 : M → Prop) (a4 : Prop) (h0 : (∀ z0 : M, (g602 (M := M) a0 a2 a3 a4 z0))) : (g603 (M := M) a0 a2 a3 a4 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e1 (u0 : M) : Prop := (t3 (a3 u0) (a4))
  let e2 (u0 : M) : Prop := (t0 (e0 u0) (e1 u0))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e5  : Prop := (t3 ((show Prop from (t14 (M := M) (a2) (fun x0_1 : M => (a3 x0_1))))) (a4))
  have v0 : ((show Prop from (t0 (e3) (e5)))) := p527 (M := M) (a2) (fun w0 : M => (a3 w0)) (a4)
  have v1 : ((show Prop from (t0 (a0) (e3)))) := p372 (M := M) (a0) (fun w0 : M => (e0 w0)) (fun w0 : M => (e1 w0)) ((fun w0 : M => h0 w0))
  have v2 : ((show Prop from (t0 (a0) (e5)))) := p10 (a0) (e3) (e5) (v0) (v1)
  exact v2
-- Actual MMB 530 dfsb2
theorem p530 (a1 : M) (a2 : M → Prop)  : (g604 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1  : Prop := (t9 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e2 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e3 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0 u1) (a2 u1))
  let e4 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e3 u0 x0_0)))
  let e5 (u0 : M) : Prop := (t0 (e0 u0) (e4 u0))
  let e6  : Prop := (t8 (M := M) (fun x0_0 : M => (e5 x0_0)))
  let e8 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e9 (u0 : M) : Prop := (t0 (e8 u0) (a2 u0))
  let e10  : Prop := (t8 (M := M) (fun x0_0 : M => (e9 x0_0)))
  let e12 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0) (e2 u0 u1))
  let e13 (u0 : M) (u1 : M) : Prop := (t0 (e8 u1) (e12 u0 u1))
  let e14 (u0 : M) (u1 : M) : Prop := (t0 (e8 u1) (e2 u0 u1))
  let e15 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0) (e14 u0 u1))
  let e16 (u0 : M) (u1 : M) : Prop := (t0 (e3 u0 u1) (e9 u1))
  let e17 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0) (e16 u0 u1))
  let e18 (u0 : M) : Prop := (t0 (e4 u0) (e10))
  let e19 (u0 : M) : Prop := (t0 (e0 u0) (e18 u0))
  let e20 (u0 : M) : Prop := (t0 (e0 u0) (e10))
  let e21 (u0 : M) : Prop := (t0 (e5 u0) (e20 u0))
  let e22 (u0 : M) : Prop := (t0 (e6) (e5 u0))
  let e23 (u0 : M) : Prop := (t0 (e6) (e20 u0))
  let e27 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0) (e8 u1))
  let e28 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0 u1) (e27 u0 u1))
  let e29 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0 u1) (e8 u1))
  let e30 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0) (e29 u0 u1))
  let e31 (u0 : M) (u1 : M) : Prop := (t0 (e9 u1) (e3 u0 u1))
  let e32 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0) (e31 u0 u1))
  let e33 (u0 : M) : Prop := (t0 (e10) (e4 u0))
  let e34 (u0 : M) : Prop := (t0 (e0 u0) (e33 u0))
  let e35 (u0 : M) : Prop := (t0 (e10) (e5 u0))
  let e39  : Prop := (t3 ((show Prop from (t14 (M := M) (a1) (fun x0_1 : M => (a2 x0_1))))) (e10))
  have v0 : (e1) := b330 (M := M) (a1)
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e6))))) := p418 (M := M) (fun w0 : M => (e5 w0))
  have v2 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e10))))) := p405 (M := M) _
  have v3 : (∀ z0 : M, (∀ z1 : M, (e13 z0 z1))) := fun z0 : M => fun z1 : M => p344 (M := M) z1 (a1) z0
  have v4 : (∀ z0 : M, (∀ z1 : M, (e15 z0 z1))) := fun z0 : M => fun z1 : M => p23 _ _ _ (v3 z0 z1)
  have v5 : (∀ z0 : M, (∀ z1 : M, (e17 z0 z1))) := fun z0 : M => fun z1 : M => p30 _ _ _ _ (v4 z0 z1)
  have v6 : (∀ z0 : M, (e19 z0)) := fun z0 : M => p368 (M := M) _ (fun w0 : M => (e3 z0 w0)) (fun w0 : M => (e9 w0)) ((fun w0 : M => v5 z0 w0))
  have v7 : (∀ z0 : M, (e21 z0)) := fun z0 : M => p5 _ _ _ (v6 z0)
  have v8 : (∀ z0 : M, (e22 z0)) := fun z0 : M => p392 (M := M) (fun w0 : M => (e5 w0)) z0
  have v9 : (∀ z0 : M, (e23 z0)) := fun z0 : M => p10 _ _ _ (v7 z0) (v8 z0)
  have v10 : ((show Prop from (t0 (e6) ((show Prop from (t0 (e1) (e10))))))) := p421 (M := M) (fun w0 : M => (e6)) (fun w0 : M => (e0 w0)) (fun w0 : M => (e10)) (v1) (v2) ((fun w0 : M => v9 w0)) 0
  have v11 : ((show Prop from (t0 (e6) (e10)))) := p7 _ _ _ (v0) (v10)
  have v12 : (∀ z0 : M, (∀ z1 : M, (e28 z0 z1))) := fun z0 : M => fun z1 : M => Eq.trans
  have v13 : (∀ z0 : M, (∀ z1 : M, (e30 z0 z1))) := fun z0 : M => fun z1 : M => p23 _ _ _ (v12 z0 z1)
  have v14 : (∀ z0 : M, (∀ z1 : M, (e32 z0 z1))) := fun z0 : M => fun z1 : M => p30 _ _ _ _ (v13 z0 z1)
  have v15 : (∀ z0 : M, (e34 z0)) := fun z0 : M => p368 (M := M) _ (fun w0 : M => (e9 w0)) (fun w0 : M => (e3 z0 w0)) ((fun w0 : M => v14 z0 w0))
  have v16 : (∀ z0 : M, (e35 z0)) := fun z0 : M => p23 _ _ _ (v15 z0)
  have v17 : ((show Prop from (t0 (e10) (e6)))) := p338 (M := M) _ (fun w0 : M => (e5 w0)) ((fun w0 : M => v16 w0))
  have v18 : ((show Prop from (t3 (e6) (e10)))) := p112 _ _ (v11) (v17)
  have v19 : (e39) := (show (e39) from v18)
  exact v19
-- Actual MMB 531 dfsb3
theorem p531 (a1 : M) (a2 : M → Prop)  : (g605 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t2 (e0 u0) (a2 u0))
  let e2  : Prop := (t9 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e4 (u0 : M) : Prop := (t1 (e1 u0))
  let e5  : Prop := (t8 (M := M) (fun x0_0 : M => (e4 x0_0)))
  let e6 (u0 : M) : Prop := (t1 (a2 u0))
  let e7 (u0 : M) : Prop := (t3 (e5) (e6 u0))
  let e9 (u0 : M) : Prop := (t3 (a2 u0) ((show Prop from (t1 (e5)))))
  let e10 (u0 : M) : Prop := (t0 (e7 u0) (e9 u0))
  let e11 (u0 : M) : Prop := (t3 (a2 u0) (e2))
  let e12 (u0 : M) : Prop := (t0 (e7 u0) (e11 u0))
  let e13 (u0 : M) : Prop := (t0 (e0 u0) (e6 u0))
  let e14  : Prop := (t8 (M := M) (fun x0_0 : M => (e13 x0_0)))
  let e15  : Prop := (t14 (M := M) (a1) (fun x0_1 : M => (e6 x0_1)))
  let e16  : Prop := (t3 (e5) (e14))
  let e17  : Prop := (t3 (e15) (e14))
  let e18  : Prop := (t3 (e5) (e15))
  let e19  : Prop := (t0 (e17) (e18))
  let e21 (u0 : M) : Prop := (t3 (e4 u0) (e13 u0))
  let e22 (u0 : M) : Prop := (t3 (e6 u0) (e15))
  let e23 (u0 : M) : Prop := (t0 (e0 u0) (e22 u0))
  let e24 (u0 : M) : Prop := (t3 (e15) (e6 u0))
  let e25 (u0 : M) : Prop := (t0 (e0 u0) (e24 u0))
  let e26 (u0 : M) : Prop := (t0 (e0 u0) (e7 u0))
  let e27 (u0 : M) : Prop := (t0 (e0 u0) (e11 u0))
  have v0 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e2))))) := p416 (M := M) (fun w0 : M => (e1 w0))
  have v1 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p128 _ _
  have v2 : (∀ z0 : M, (e12 z0)) := (show (∀ z0 : M, (e12 z0)) from v1)
  have v3 : ((show Prop from (t0 (e16) (e19)))) := p152 _ _ _
  have v4 : (∀ z0 : M, (e21 z0)) := fun z0 : M => p272 _ _
  have v5 : (e16) := p367 (M := M) (fun w0 : M => (e4 w0)) (fun w0 : M => (e13 w0)) ((fun w0 : M => v4 w0))
  have v6 : (e19) := ((v3) (v5))
  have v7 : (e17) := p530 (M := M) (a1) (fun w0 : M => (e6 w0))
  have v8 : (e18) := ((v6) (v7))
  have v9 : (∀ z0 : M, (e23 z0)) := fun z0 : M => p516 (M := M) (a1) (fun w0 : M => (e6 w0)) z0
  have v10 : (∀ z0 : M, (e25 z0)) := fun z0 : M => p144 _ _ _ (v9 z0)
  have v11 : (∀ z0 : M, (e26 z0)) := fun z0 : M => p157 _ _ _ _ (v8) (v10 z0)
  have v12 : (∀ z0 : M, (e27 z0)) := fun z0 : M => p10 _ _ _ (v2 z0) (v11 z0)
  have v13 : ((show Prop from (t3 ((show Prop from (t14 (M := M) (a1) (fun x0_1 : M => (a2 x0_1))))) (e2)))) := p526 (M := M) (a1) (fun w0 : M => (a2 w0)) (fun w0 : M => (e2)) (v0) ((fun w0 : M => v12 w0)) 0
  exact v13
-- Actual MMB 532 sbco
theorem p532 (a2 : M → M) (a3 : M → Prop)  : (∀ z0 : M, (g606 (M := M) a2 a3 z0)) := by
  let e0 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a3 x0_1)))
  let e1 (u0 : M) : Prop := (t14 (M := M) (a2 u0) (fun x0_1 : M => (e0 x0_1)))
  let e2 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 (a2 u0))
  let e3 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0 u1) (e0 u1))
  let e4 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e3 u0 x0_0)))
  let e5 (u0 : M) : Prop := (t14 (M := M) (a2 u0) (fun x0_1 : M => (a3 x0_1)))
  let e6 (u0 : M) : Prop := (t3 (e1 u0) (e4 u0))
  let e7 (u0 : M) : Prop := (t3 (e4 u0) (e5 u0))
  let e8 (u0 : M) : Prop := (t3 (e1 u0) (e5 u0))
  let e9 (u0 : M) : Prop := (t0 (e7 u0) (e8 u0))
  let e10 (u0 : M) : Prop := (t0 (e6 u0) (e9 u0))
  let e11 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e12 (u0 : M) (u1 : M) : Prop := (t0 (e11 u0 u1) (a3 u0))
  let e13 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e12 x0_0 u0)))
  let e14 (u0 : M) : Prop := (t3 (e0 u0) (e13 u0))
  let e15 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0 u1) (e13 u1))
  let e16 (u0 : M) (u1 : M) : Prop := (t3 (e3 u0 u1) (e15 u0 u1))
  let e17 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e15 u0 x0_0)))
  let e18 (u0 : M) : Prop := (t3 (e4 u0) (e17 u0))
  have v0 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p149 (e1 z0) (e4 z0) (e5 z0)
  have v1 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p530 (M := M) (a2 z0) (fun w0 : M => (e0 w0))
  have v2 : (∀ z0 : M, (e9 z0)) := fun z0 : M => b3 (e6 z0) (e9 z0) (v0 z0) (v1 z0)
  have v3 : (∀ z0 : M, (e14 z0)) := fun z0 : M => p530 (M := M) z0 (fun w0 : M => (a3 w0))
  have v4 : (∀ z0 : M, (∀ z1 : M, (e16 z0 z1))) := fun z0 : M => fun z1 : M => p194 (e2 z0 z1) (e0 z1) (e13 z1) (v3 z1)
  have v5 : (∀ z0 : M, (e18 z0)) := fun z0 : M => p367 (M := M) (fun w0 : M => (e3 z0 w0)) (fun w0 : M => (e15 z0 w0)) ((fun w0 : M => v4 z0 w0))
  have v6 : (∀ z0 : M, (e7 z0)) := (show (∀ z0 : M, (e7 z0)) from v5)
  have v7 : (∀ z0 : M, (e8 z0)) := fun z0 : M => b3 (e7 z0) (e8 z0) (v2 z0) (v6 z0)
  exact v7
-- Actual MMB 533 sbid
theorem p533 (a1 : M → Prop)  : (∀ z0 : M, (g607 (M := M) a1 z0)) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e1 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (e0 x0_0 u0)))
  let e2 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e3 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0 u1) (a1 u1))
  let e4 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e3 u0 x0_0)))
  let e5 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e4 u0))
  let e6 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e5 x0_0 u0)))
  let e7 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e6 u0)))
  let e8 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a1 u0)))
  let e9 (u0 : M) (u1 : M) : Prop := (t0 (e6 u1) (e5 u0 u1))
  let e10 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e2 u0 u1))
  let e11 (u0 : M) (u1 : M) : Prop := (t0 (e4 u0) (e3 u0 u1))
  let e12 (u0 : M) (u1 : M) : Prop := (t0 (e4 u0) (a1 u1))
  let e13 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0 u1) (e12 u0 u1))
  let e14 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e12 u0 u1))
  let e15 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (a1 u1))
  let e16 (u0 : M) (u1 : M) : Prop := (t0 (e5 u0 u1) (e15 u0 u1))
  let e17 (u0 : M) (u1 : M) : Prop := (t0 (e6 u1) (e15 u0 u1))
  let e18 (u0 : M) : Prop := (t0 (e1 u0) (a1 u0))
  let e19 (u0 : M) : Prop := (t0 (e6 u0) (e18 u0))
  let e20 (u0 : M) : Prop := (t0 (e6 u0) (a1 u0))
  let e21 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a1 x0_1)))
  let e22 (u0 : M) : Prop := (t3 (e21 u0) (e4 u0))
  let e23 (u0 : M) (u1 : M) : Prop := (t3 (a1 u1) (e21 u0))
  let e24 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0 u1) (e23 u0 u1))
  let e25 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e23 u0 u1))
  let e26 (u0 : M) (u1 : M) : Prop := (t3 (a1 u1) (e4 u0))
  let e27 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e26 u0 u1))
  let e28 (u0 : M) (u1 : M) : Prop := (t0 (a1 u1) (e4 u0))
  let e29 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e28 u0 u1))
  let e30 (u0 : M) (u1 : M) : Prop := (t0 (a1 u1) (e5 u0 u1))
  let e31 (u0 : M) : Prop := (t0 (a1 u0) (e6 u0))
  let e32 (u0 : M) : Prop := (t3 (e6 u0) (a1 u0))
  let e33 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a1 x0_1)))
  let e34 (u0 : M) : Prop := (t3 (e33 u0) (a1 u0))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => b330 (M := M) z0
  have v1 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p418 (M := M) (fun w0 : M => (e5 w0 z0))
  have v2 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p405 (M := M) (a1 z0)
  have v3 : (∀ z0 : M, (∀ z1 : M, (e9 z0 z1))) := fun z0 : M => fun z1 : M => p392 (M := M) (fun w0 : M => (e5 w0 z1)) z0
  have v4 : (∀ z0 : M, (∀ z1 : M, (e10 z0 z1))) := fun z0 : M => fun z1 : M => p341 (M := M) z0 z1
  have v5 : (∀ z0 : M, (∀ z1 : M, (e11 z0 z1))) := fun z0 : M => fun z1 : M => p392 (M := M) (fun w0 : M => (e3 z0 w0)) z1
  have v6 : (∀ z0 : M, (∀ z1 : M, (e13 z0 z1))) := fun z0 : M => fun z1 : M => p23 (e4 z0) (e2 z0 z1) (a1 z1) (v5 z0 z1)
  have v7 : (∀ z0 : M, (∀ z1 : M, (e14 z0 z1))) := fun z0 : M => fun z1 : M => p11 (e0 z0 z1) (e2 z0 z1) (e12 z0 z1) (v4 z0 z1) (v6 z0 z1)
  have v8 : (∀ z0 : M, (∀ z1 : M, (e16 z0 z1))) := fun z0 : M => fun z1 : M => p5 (e0 z0 z1) (e4 z0) (a1 z1) (v7 z0 z1)
  have v9 : (∀ z0 : M, (∀ z1 : M, (e17 z0 z1))) := fun z0 : M => fun z1 : M => p11 (e6 z1) (e5 z0 z1) (e15 z0 z1) (v3 z0 z1) (v8 z0 z1)
  have v10 : (∀ z0 : M, (e19 z0)) := fun z0 : M => p421 (M := M) (fun w0 : M => (e6 z0)) (fun w0 : M => (e0 w0 z0)) (fun w0 : M => (a1 z0)) (v1 z0) (v2 z0) ((fun w0 : M => v9 w0 z0)) 0
  have v11 : (∀ z0 : M, (e20 z0)) := fun z0 : M => p7 (e6 z0) (e1 z0) (a1 z0) (v0 z0) (v10 z0)
  have v12 : (∀ z0 : M, (e22 z0)) := fun z0 : M => p530 (M := M) z0 (fun w0 : M => (a1 w0))
  have v13 : (∀ z0 : M, (∀ z1 : M, (e24 z0 z1))) := fun z0 : M => fun z1 : M => p516 (M := M) z0 (fun w0 : M => (a1 w0)) z1
  have v14 : (∀ z0 : M, (∀ z1 : M, (e25 z0 z1))) := fun z0 : M => fun z1 : M => p10 (e0 z0 z1) (e2 z0 z1) (e23 z0 z1) (v13 z0 z1) (v4 z0 z1)
  have v15 : (∀ z0 : M, (∀ z1 : M, (e27 z0 z1))) := fun z0 : M => fun z1 : M => p159 (e0 z0 z1) (a1 z1) (e21 z0) (e4 z0) (v12 z0) (v14 z0 z1)
  have v16 : (∀ z0 : M, (∀ z1 : M, (e29 z0 z1))) := fun z0 : M => fun z1 : M => p106 (e0 z0 z1) (a1 z1) (e4 z0) (v15 z0 z1)
  have v17 : (∀ z0 : M, (∀ z1 : M, (e30 z0 z1))) := fun z0 : M => fun z1 : M => p23 (e0 z0 z1) (a1 z1) (e4 z0) (v16 z0 z1)
  have v18 : (∀ z0 : M, (e31 z0)) := fun z0 : M => p338 (M := M) (a1 z0) (fun w0 : M => (e5 w0 z0)) ((fun w0 : M => v17 w0 z0))
  have v19 : (∀ z0 : M, (e32 z0)) := fun z0 : M => p112 (e6 z0) (a1 z0) (v11 z0) (v18 z0)
  have v20 : (∀ z0 : M, (e34 z0)) := (show (∀ z0 : M, (e34 z0)) from v19)
  exact v20
-- Actual MMB 534 sbcom
theorem p539 (a2 : M) (a3 : M → M → Prop) (a4 : M → M → Prop) (h0 : (∀ z0 : M, (g620 (M := M) a2 a3 a4 z0))) (h1 : (∀ z0 : M, (g621 (M := M) a2 a3 a4 z0))) (h2 : (∀ z0 : M, (∀ z1 : M, (g622 (M := M) a2 a3 a4 z0 z1)))) : (∀ z0 : M, (∀ z1 : M, (g623 (M := M) a2 a3 a4 z0 z1))) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e1 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0 u1)))
  let e2 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e0 u0 u1) (a3 u1 u2))
  let e3 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0 u1 x0_0)))
  let e4 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e5 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e4 u0 u1)))
  let e6 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e4 u0 u2) (a4 u1 u2))
  let e7 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e6 u0 x0_0 u1)))
  let e8 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e9 (u0 : M) (u1 : M) (u2 : M) : Prop := (t3 (e0 u0 u1) (e4 u0 u2))
  let e10 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e8 u1 u2) (e9 u0 u1 u2))
  let e11 (u0 : M) (u1 : M) (u2 : M) : Prop := (t3 (e2 u0 u1 u2) (e6 u0 u1 u2))
  let e12 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e8 u1 u2) (e11 u0 u1 u2))
  let e13 (u0 : M) (u1 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e2 u0 x0_0 u1)))
  let e14 (u0 : M) (u1 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e6 u0 u1 x0_0)))
  let e15 (u0 : M) (u1 : M) (u2 : M) : Prop := (t3 (e13 u0 u2) (e14 u0 u1))
  let e16 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e17 (u0 : M) (u1 : M) : Prop := (t0 (e16 u0) (e13 u0 u1))
  let e18 (u0 : M) (u1 : M) : Prop := (t0 (e16 u0) (e14 u0 u1))
  let e19 (u0 : M) (u1 : M) (u2 : M) : Prop := (t3 (e17 u0 u2) (e18 u0 u1))
  let e20 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e17 x0_0 u0)))
  let e21 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e18 x0_0 u0)))
  let e22 (u0 : M) (u1 : M) : Prop := (t3 (e20 u1) (e21 u0))
  let e23 (u0 : M) : Prop := (t14 (M := M) (a2) (fun x0_1 : M => (a3 x0_1 u0)))
  let e24 (u0 : M) : Prop := (t14 (M := M) (a2) (fun x0_1 : M => (a4 u0 x0_1)))
  let e25 (u0 : M) (u1 : M) : Prop := (t3 (e23 u1) (e24 u0))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e1 z0 z1))) := fun z0 : M => fun z1 : M => p405 (M := M) (e0 z0 z1)
  have v1 : (∀ z0 : M, (∀ z1 : M, (e3 z0 z1))) := fun z0 : M => fun z1 : M => p412 (M := M) (fun w0 : M => (e0 z0 z1)) (fun w0 : M => (a3 z1 w0)) (v0 z0 z1) (h0 z1)
  have v2 : (∀ z0 : M, (∀ z1 : M, (e5 z0 z1))) := fun z0 : M => fun z1 : M => p405 (M := M) (e4 z0 z1)
  have v3 : (∀ z0 : M, (∀ z1 : M, (e7 z0 z1))) := fun z0 : M => fun z1 : M => p412 (M := M) (fun w0 : M => (e4 z0 z1)) (fun w0 : M => (a4 w0 z1)) (v2 z0 z1) (h1 z1)
  have v4 : (∀ z0 : M, (∀ z1 : M, (∀ z2 : M, (e10 z0 z1 z2)))) := fun z0 : M => fun z1 : M => fun z2 : M => p346 (M := M) z1 z2 z0
  have v5 : (∀ z0 : M, (∀ z1 : M, (∀ z2 : M, (e12 z0 z1 z2)))) := fun z0 : M => fun z1 : M => fun z2 : M => p188 (e8 z1 z2) (e0 z0 z1) (e4 z0 z2) (a3 z1 z2) (a4 z1 z2) (v4 z0 z1 z2) (h2 z1 z2)
  have v6 : (∀ z0 : M, (∀ z1 : M, (∀ z2 : M, (e15 z0 z1 z2)))) := fun z0 : M => fun z1 : M => fun z2 : M => p480 (M := M) (fun w0 : M => (fun w1 : M => (e2 z0 w0 w1))) (fun w0 : M => (fun w1 : M => (e6 z0 w0 w1))) ((fun w0 : M => v1 z0 w0)) ((fun w1 : M => v3 z0 w1)) ((fun w0 : M => (fun w1 : M => v5 z0 w0 w1))) z1 z2
  have v7 : (∀ z0 : M, (∀ z1 : M, (∀ z2 : M, (e19 z0 z1 z2)))) := fun z0 : M => fun z1 : M => fun z2 : M => p194 (e16 z0) (e13 z0 z2) (e14 z0 z1) (v6 z0 z1 z2)
  have v8 : (∀ z0 : M, (∀ z1 : M, (e22 z0 z1))) := fun z0 : M => fun z1 : M => p367 (M := M) (fun w0 : M => (e17 w0 z1)) (fun w0 : M => (e18 w0 z0)) ((fun w0 : M => v7 w0 z0 z1))
  have v9 : (∀ z0 : M, (∀ z1 : M, (e25 z0 z1))) := (show (∀ z0 : M, (∀ z1 : M, (e25 z0 z1))) from v8)
  exact v9
-- Actual MMB 540 cbvsb
theorem p541 (a1 : M) (a2 : M → Prop) (a3 : Prop) (h0 : (∀ z0 : M, (g468 (M := M) a1 a2 a3 z0))) : (g626 (M := M) a1 a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t0 (e0 u0) (a2 u0))
  let e2  : Prop := (t8 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e3  : Prop := (t14 (M := M) (a1) (fun x0_1 : M => (a2 x0_1)))
  let e4  : Prop := (t3 (e3) (e2))
  let e5  : Prop := (t3 (e3) (a3))
  let e6  : Prop := (t3 (e2) (a3))
  let e7  : Prop := (t0 (e5) (e6))
  have v0 : ((show Prop from (t0 (e4) (e7)))) := p151 (e2) (e3) (a3)
  have v1 : (e4) := p530 (M := M) (a1) (fun w0 : M => (a2 w0))
  have v2 : (e7) := b3 (e4) (e7) (v0) (v1)
  have v3 : (e5) := p528 (M := M) (a1) (fun w0 : M => (a2 w0)) (a3) ((fun w0 : M => h0 w0))
  have v4 : (e6) := b3 (e5) (e6) (v2) (v3)
  exact v4
-- Actual MMB 542 aleqed
theorem p543 (a1 : M) (a2 : M → Prop) (a3 : Prop) (h0 : (∀ z0 : M, (g468 (M := M) a1 a2 a3 z0))) : (g628 (M := M) a1 a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t2 (e0 u0) (a2 u0))
  let e2  : Prop := (t9 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e3  : Prop := (t14 (M := M) (a1) (fun x0_1 : M => (a2 x0_1)))
  let e4  : Prop := (t3 (e3) (e2))
  let e5  : Prop := (t3 (e3) (a3))
  let e6  : Prop := (t3 (e2) (a3))
  let e7  : Prop := (t0 (e5) (e6))
  have v0 : ((show Prop from (t0 (e4) (e7)))) := p151 (e2) (e3) (a3)
  have v1 : (e4) := p531 (M := M) (a1) (fun w0 : M => (a2 w0))
  have v2 : (e7) := b3 (e4) (e7) (v0) (v1)
  have v3 : (e5) := p528 (M := M) (a1) (fun w0 : M => (a2 w0)) (a3) ((fun w0 : M => h0 w0))
  have v4 : (e6) := b3 (e5) (e6) (v2) (v3)
  exact v4
-- Actual MMB 544 exeqed
theorem p547 (a2 : M → Prop)  : (g632 (M := M) a2 ) := by
  let e0 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a2 u0)))
  let e1 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a2 x0_1)))
  let e2 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e1 u0)))
  let e3 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e4 (u0 : M) (u1 : M) : Prop := (t3 (a2 u0) (e1 u1))
  let e5 (u0 : M) (u1 : M) : Prop := (t0 (e3 u0 u1) (e4 u0 u1))
  have v0 : (∀ z0 : M, (e0 z0)) := fun z0 : M => p405 (M := M) (a2 z0)
  have v1 : (∀ z0 : M, (e2 z0)) := fun z0 : M => p518 (M := M) z0 (fun w0 : M => (a2 w0))
  have v2 : (∀ z0 : M, (∀ z1 : M, (e5 z0 z1))) := fun z0 : M => fun z1 : M => p516 (M := M) z1 (fun w0 : M => (a2 w0)) z0
  have v3 : ((show Prop from (t3 ((show Prop from (t8 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e1 x0_0)))))))) := p480 (M := M) (fun w0 : M => (fun w1 : M => (a2 w0))) (fun w0 : M => (fun w1 : M => (e1 w1))) ((fun w0 : M => v0 w0)) ((fun w1 : M => v1 w1)) ((fun w0 : M => (fun w1 : M => v2 w0 w1))) 0 0
  exact v3
-- Actual MMB 548 cbvexs
theorem p548 (a2 : M → Prop)  : (g633 (M := M) a2 ) := by
  let e0 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a2 u0)))
  let e1 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a2 x0_1)))
  let e2 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e1 u0)))
  let e3 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e4 (u0 : M) (u1 : M) : Prop := (t3 (a2 u0) (e1 u1))
  let e5 (u0 : M) (u1 : M) : Prop := (t0 (e3 u0 u1) (e4 u0 u1))
  have v0 : (∀ z0 : M, (e0 z0)) := fun z0 : M => p405 (M := M) (a2 z0)
  have v1 : (∀ z0 : M, (e2 z0)) := fun z0 : M => p518 (M := M) z0 (fun w0 : M => (a2 w0))
  have v2 : (∀ z0 : M, (∀ z1 : M, (e5 z0 z1))) := fun z0 : M => fun z1 : M => p516 (M := M) z1 (fun w0 : M => (a2 w0)) z0
  have v3 : ((show Prop from (t3 ((show Prop from (t9 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show Prop from (t9 (M := M) (fun x0_0 : M => (e1 x0_0)))))))) := p482 (M := M) (fun w0 : M => (fun w1 : M => (a2 w0))) (fun w0 : M => (fun w1 : M => (e1 w1))) ((fun w0 : M => v0 w0)) ((fun w1 : M => v1 w1)) ((fun w0 : M => (fun w1 : M => v2 w0 w1))) 0 0
  exact v3
-- Actual MMB 549 cbvald
theorem p549 (a2 : Prop) (a3 : M → Prop) (a4 : M → Prop) (h0 : (∀ z0 : M, (∀ z1 : M, (g634 (M := M) a2 a3 a4 z0 z1)))) : (g635 (M := M) a2 a3 a4 ) := by
  let e0  : Prop := (t8 (M := M) (fun x0_0 : M => (a3 x0_0)))
  let e1 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a3 x0_1)))
  let e2  : Prop := (t8 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e3  : Prop := (t3 (e0) (e2))
  let e5 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e6 (u0 : M) (u1 : M) : Prop := (t3 (a3 u0) (a4 u1))
  let e7 (u0 : M) (u1 : M) : Prop := (t0 (e5 u0 u1) (e6 u0 u1))
  let e8 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e7 x0_0 u0)))
  let e9 (u0 : M) : Prop := (t3 (e1 u0) (a4 u0))
  let e10 (u0 : M) : Prop := (t0 (e8 u0) (e9 u0))
  let e11 (u0 : M) : Prop := (t0 (a2) (e8 u0))
  let e12 (u0 : M) : Prop := (t0 (a2) (e9 u0))
  let e13  : Prop := (t8 (M := M) (fun x0_0 : M => (a4 x0_0)))
  have v0 : (e3) := p547 (M := M) (fun w0 : M => (a3 w0))
  have v1 : ((show Prop from (t0 (a2) (e3)))) := p4 (a2) (e3) (v0)
  have v2 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p527 (M := M) z0 (fun w0 : M => (a3 w0)) (a4 z0)
  have v3 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p372 (M := M) (a2) (fun w0 : M => (e5 w0 z0)) (fun w0 : M => (e6 w0 z0)) ((fun w0 : M => h0 w0 z0))
  have v4 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p10 (a2) (e8 z0) (e9 z0) (v2 z0) (v3 z0)
  have v5 : ((show Prop from (t0 (a2) ((show Prop from (t3 (e2) (e13))))))) := p371 (M := M) (a2) (fun w1 : M => (e1 w1)) (fun w1 : M => (a4 w1)) ((fun w1 : M => v4 w1))
  have v6 : ((show Prop from (t0 (a2) ((show Prop from (t3 (e0) (e13))))))) := p145 (a2) (e0) (e2) (e13) (v1) (v5)
  exact v6
-- Actual MMB 550 cbvexd
theorem p550 (a2 : Prop) (a3 : M → Prop) (a4 : M → Prop) (h0 : (∀ z0 : M, (∀ z1 : M, (g634 (M := M) a2 a3 a4 z0 z1)))) : (g636 (M := M) a2 a3 a4 ) := by
  let e0  : Prop := (t9 (M := M) (fun x0_0 : M => (a3 x0_0)))
  let e1 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a3 x0_1)))
  let e2  : Prop := (t9 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e3  : Prop := (t3 (e0) (e2))
  let e5 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e6 (u0 : M) (u1 : M) : Prop := (t3 (a3 u0) (a4 u1))
  let e7 (u0 : M) (u1 : M) : Prop := (t0 (e5 u0 u1) (e6 u0 u1))
  let e8 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e7 x0_0 u0)))
  let e9 (u0 : M) : Prop := (t3 (e1 u0) (a4 u0))
  let e10 (u0 : M) : Prop := (t0 (e8 u0) (e9 u0))
  let e11 (u0 : M) : Prop := (t0 (a2) (e8 u0))
  let e12 (u0 : M) : Prop := (t0 (a2) (e9 u0))
  let e13  : Prop := (t9 (M := M) (fun x0_0 : M => (a4 x0_0)))
  have v0 : (e3) := p548 (M := M) (fun w0 : M => (a3 w0))
  have v1 : ((show Prop from (t0 (a2) (e3)))) := p4 (a2) (e3) (v0)
  have v2 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p527 (M := M) z0 (fun w0 : M => (a3 w0)) (a4 z0)
  have v3 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p372 (M := M) (a2) (fun w0 : M => (e5 w0 z0)) (fun w0 : M => (e6 w0 z0)) ((fun w0 : M => h0 w0 z0))
  have v4 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p10 (a2) (e8 z0) (e9 z0) (v2 z0) (v3 z0)
  have v5 : ((show Prop from (t0 (a2) ((show Prop from (t3 (e2) (e13))))))) := p379 (M := M) (a2) (fun w1 : M => (e1 w1)) (fun w1 : M => (a4 w1)) ((fun w1 : M => v4 w1))
  have v6 : ((show Prop from (t0 (a2) ((show Prop from (t3 (e0) (e13))))))) := p145 (a2) (e0) (e2) (e13) (v1) (v5)
  exact v6
-- Actual MMB 551 pimexeqed
theorem p554 (a0 : (M → Prop))  : (g640 (M := M) a0 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e1 (u0 : M) : Prop := (t3 (e0 u0) (e0 u0))
  let e3  : Prop := (t17 (M := M) (a0) (a0))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p115 (e0 z0)
  have v1 : ((show Prop from (t8 (M := M) (fun x0_0 : M => (e1 x0_0))))) := b325 (M := M) (fun w0 : M => (e1 w0)) ((fun w0 : M => v0 w0))
  have v2 : (e3) := (show (e3) from v1)
  exact v2
-- Actual MMB 555 eqscom
theorem p555 (a0 : (M → Prop)) (a1 : (M → Prop))  : (g641 (M := M) a0 a1 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e2 (u0 : M) : Prop := (t3 (e0 u0) (e1 u0))
  let e3 (u0 : M) : Prop := (t3 (e1 u0) (e0 u0))
  let e4 (u0 : M) : Prop := (t0 (e2 u0) (e3 u0))
  let e10  : Prop := (t0 ((show Prop from (t17 (M := M) (a0) (a1)))) ((show Prop from (t17 (M := M) (a1) (a0)))))
  have v0 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p142 (e0 z0) (e1 z0)
  have v1 : ((show Prop from (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e2 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e3 x0_0)))))))) := p337 (M := M) (fun w0 : M => (e2 w0)) (fun w0 : M => (e3 w0)) ((fun w0 : M => v0 w0))
  have v2 : (e10) := (show (e10) from v1)
  exact v2
-- Actual MMB 556 eqscomb
theorem p556 (a0 : (M → Prop)) (a1 : (M → Prop))  : (g642 (M := M) a0 a1 ) := by
  let e0  : Prop := (t17 (M := M) (a0) (a1))
  let e1  : Prop := (t17 (M := M) (a1) (a0))
  have v0 : ((show Prop from (t0 (e0) (e1)))) := p555 (M := M) (a0) (a1)
  have v1 : ((show Prop from (t0 (e1) (e0)))) := p555 (M := M) (a1) (a0)
  have v2 : ((show Prop from (t3 (e0) (e1)))) := p112 (e0) (e1) (v0) (v1)
  exact v2
-- Actual MMB 557 eqstr
theorem p557 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : (g643 (M := M) a0 a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e2 (u0 : M) : Prop := (t16 (M := M) u0 (a2))
  let e3 (u0 : M) : Prop := (t3 (e0 u0) (e1 u0))
  let e4 (u0 : M) : Prop := (t3 (e1 u0) (e2 u0))
  let e5 (u0 : M) : Prop := (t3 (e0 u0) (e2 u0))
  let e6 (u0 : M) : Prop := (t0 (e4 u0) (e5 u0))
  let e7 (u0 : M) : Prop := (t0 (e3 u0) (e6 u0))
  let e17  : Prop := (t0 ((show Prop from (t17 (M := M) (a0) (a1)))) ((show Prop from (t0 ((show Prop from (t17 (M := M) (a1) (a2)))) ((show Prop from (t17 (M := M) (a0) (a2))))))))
  have v0 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p149 _ _ _
  have v1 : ((show Prop from (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e3 x0_0))))) ((show Prop from (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e4 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e5 x0_0))))))))))) := p370 (M := M) (fun w0 : M => (e3 w0)) (fun w0 : M => (e4 w0)) (fun w0 : M => (e5 w0)) ((fun w0 : M => v0 w0))
  have v2 : (e17) := (show (e17) from v1)
  exact v2
-- Actual MMB 558 eqstr2
theorem p559 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : (g645 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t17 (M := M) (a0) (a1))
  let e3  : Prop := (t0 ((show Prop from (t17 (M := M) (a1) (a2)))) ((show Prop from (t17 (M := M) (a0) (a2)))))
  let e5  : Prop := (t17 (M := M) (a1) (a0))
  have v0 : ((show Prop from (t0 (e0) (e3)))) := p557 (M := M) (a0) (a1) (a2)
  have v1 : ((show Prop from (t0 (e5) (e0)))) := p555 (M := M) (a1) (a0)
  have v2 : ((show Prop from (t0 (e5) (e3)))) := p10 (e5) (e0) (e3) (v0) (v1)
  exact v2
-- Actual MMB 560 eqstr4
theorem p560 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : (g646 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t17 (M := M) (a2) (a1))
  let e1  : Prop := (t17 (M := M) (a1) (a2))
  let e3  : Prop := (t17 (M := M) (a0) (a1))
  let e4  : Prop := (t17 (M := M) (a0) (a2))
  have v0 : ((show Prop from (t0 (e0) (e1)))) := p555 (M := M) (a2) (a1)
  have v1 : ((show Prop from (t0 (e3) ((show Prop from (t0 (e1) (e4))))))) := p557 (M := M) (a0) (a1) (a2)
  have v2 : ((show Prop from (t0 (e3) ((show Prop from (t0 (e0) (e4))))))) := p17 (e3) (e0) (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 561 eqstr3d
theorem p561 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop) (h0 : (g647 (M := M) a0 a1 a2 a3 )) (h1 : (g648 (M := M) a0 a1 a2 a3 )) : (g649 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t17 (M := M) (a1) (a0))
  let e1  : Prop := (t17 (M := M) (a1) (a2))
  let e2  : Prop := (t17 (M := M) (a0) (a2))
  have v0 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e1) (e2))))))) := p559 (M := M) (a0) (a1) (a2)
  have v1 : ((show Prop from (t0 (a3) (e2)))) := p15 (a3) (e0) (e1) (e2) (v0) (h0) (h1)
  exact v1
-- Actual MMB 562 eqsidd
theorem p562 (a0 : Prop) (a1 : (M → Prop))  : (g650 (M := M) a0 a1 ) := by
  let e0  : Prop := (t17 (M := M) (a1) (a1))
  have v0 : (e0) := p554 (M := M) (a1)
  have v1 : ((show Prop from (t0 (a0) (e0)))) := p4 (a0) (e0) (v0)
  exact v1
-- Actual MMB 563 eqscomd
theorem p563 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : Prop) (h0 : (g651 (M := M) a0 a1 a2 )) : (g652 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t17 (M := M) (a0) (a1))
  let e1  : Prop := (t17 (M := M) (a1) (a0))
  have v0 : ((show Prop from (t0 (e0) (e1)))) := p555 (M := M) (a0) (a1)
  have v1 : ((show Prop from (t0 (a2) (e1)))) := p10 (a2) (e0) (e1) (v0) (h0)
  exact v1
-- Actual MMB 564 eqstrd
theorem p564 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop) (h0 : (g653 (M := M) a0 a1 a2 a3 )) (h1 : (g648 (M := M) a0 a1 a2 a3 )) : (g649 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t17 (M := M) (a0) (a1))
  let e1  : Prop := (t17 (M := M) (a1) (a2))
  let e2  : Prop := (t17 (M := M) (a0) (a2))
  have v0 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e1) (e2))))))) := p557 (M := M) (a0) (a1) (a2)
  have v1 : ((show Prop from (t0 (a3) (e2)))) := p15 (a3) (e0) (e1) (e2) (v0) (h0) (h1)
  exact v1
-- Actual MMB 565 eqstr4d
theorem p565 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop) (h0 : (g653 (M := M) a0 a1 a2 a3 )) (h1 : (g654 (M := M) a0 a1 a2 a3 )) : (g649 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t17 (M := M) (a0) (a1))
  let e1  : Prop := (t17 (M := M) (a2) (a1))
  let e2  : Prop := (t17 (M := M) (a0) (a2))
  have v0 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e1) (e2))))))) := p560 (M := M) (a0) (a1) (a2)
  have v1 : ((show Prop from (t0 (a3) (e2)))) := p15 (a3) (e0) (e1) (e2) (v0) (h0) (h1)
  exact v1
-- Actual MMB 566 syl5eqs
theorem p566 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop) (h0 : (g655 (M := M) a0 a1 a2 a3 )) (h1 : (g648 (M := M) a0 a1 a2 a3 )) : (g649 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t17 (M := M) (a0) (a1))
  have v0 : ((show Prop from (t0 (a3) (e0)))) := p4 (a3) (e0) (h0)
  have v1 : ((show Prop from (t0 (a3) ((show Prop from (t17 (M := M) (a0) (a2))))))) := p564 (M := M) (a0) (a1) (a2) (a3) (v0) (h1)
  exact v1
-- Actual MMB 567 syl5eqsr
theorem p568 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop) (h0 : (g657 (M := M) a0 a1 a2 a3 )) (h1 : (g653 (M := M) a0 a1 a2 a3 )) : (g649 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t17 (M := M) (a1) (a2))
  have v0 : ((show Prop from (t0 (a3) (e0)))) := p4 (a3) (e0) (h0)
  have v1 : ((show Prop from (t0 (a3) ((show Prop from (t17 (M := M) (a0) (a2))))))) := p564 (M := M) (a0) (a1) (a2) (a3) (h1) (v0)
  exact v1
-- Actual MMB 569 syl6eqsr
theorem p569 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : Prop) (h0 : (g658 (M := M) a0 a1 a2 a3 )) (h1 : (g653 (M := M) a0 a1 a2 a3 )) : (g649 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t17 (M := M) (a2) (a1))
  have v0 : ((show Prop from (t0 (a3) (e0)))) := p4 (a3) (e0) (h0)
  have v1 : ((show Prop from (t0 (a3) ((show Prop from (t17 (M := M) (a0) (a2))))))) := p565 (M := M) (a0) (a1) (a2) (a3) (h1) (v0)
  exact v1
-- Actual MMB 570 eqstr3g
theorem p571 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : Prop) (h0 : (g663 (M := M) a0 a1 a2 a3 a4 )) (h1 : (g664 (M := M) a0 a1 a2 a3 a4 )) (h2 : (g661 (M := M) a0 a1 a2 a3 a4 )) : (g662 (M := M) a0 a1 a2 a3 a4 ) := by
  have v0 : ((show Prop from (t0 (a4) ((show Prop from (t17 (M := M) (a0) (a3))))))) := p569 (M := M) (a0) (a1) (a3) (a4) (h1) (h2)
  have v1 : ((show Prop from (t0 (a4) ((show Prop from (t17 (M := M) (a2) (a3))))))) := p566 (M := M) (a2) (a0) (a3) (a4) (h0) (v0)
  exact v1
-- Actual MMB 572 eleq1
theorem p572 (a0 : (M → Prop)) (a1 : M) (a2 : M)  : (g665 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  let e1  : Prop := (t16 (M := M) (a1) (a0))
  let e2  : Prop := (t16 (M := M) (a2) (a0))
  let e5  : Prop := (t10 (M := M) (a2) (a1))
  let e6  : Prop := (t0 (e2) (e1))
  have v0 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e1) (e2))))))) := b553 (M := M) (a1) (a2) (a0)
  have v1 : ((show Prop from (t0 (e5) (e6)))) := b553 (M := M) (a2) (a1) (a0)
  have v2 : ((show Prop from (t0 (e0) (e5)))) := p341 (M := M) (a1) (a2)
  have v3 : ((show Prop from (t0 (e0) (e6)))) := p10 _ _ _ (v1) (v2)
  have v4 : ((show Prop from (t0 (e0) ((show Prop from (t3 (e1) (e2))))))) := p113 _ _ _ (v0) (v3)
  exact v4
-- Actual MMB 573 eleq2
theorem p573 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : M)  : (g666 (M := M) a0 a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e2  : Prop := (t16 (M := M) (a2) (a0))
  let e3 (u0 : M) : Prop := (t3 (e1 u0) (e2))
  let e4 (u0 : M) : Prop := (t0 (e0 u0) (e3 u0))
  let e5 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e6  : Prop := (t16 (M := M) (a2) (a1))
  let e7 (u0 : M) : Prop := (t3 (e5 u0) (e6))
  let e8 (u0 : M) : Prop := (t0 (e0 u0) (e7 u0))
  let e9 (u0 : M) : Prop := (t3 (e1 u0) (e5 u0))
  let e10  : Prop := (t3 (e2) (e6))
  let e11 (u0 : M) : Prop := (t3 (e9 u0) (e10))
  let e12 (u0 : M) : Prop := (t0 (e0 u0) (e11 u0))
  let e16  : Prop := (t0 ((show Prop from (t17 (M := M) (a0) (a1)))) (e10))
  have v0 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p572 (M := M) (a0) z0 (a2)
  have v1 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p572 (M := M) (a1) z0 (a2)
  have v2 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p233 (e0 z0) (e1 z0) (e2) (e5 z0) (e6) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e9 x0_0))))) (e10)))) := p440 (M := M) (a2) (fun w0 : M => (e9 w0)) (e10) ((fun w0 : M => v2 w0))
  have v4 : (e16) := (show (e16) from v3)
  exact v4
-- Actual MMB 574 eleq1d
theorem p574 (a0 : Prop) (a1 : M) (a2 : M) (a3 : (M → Prop)) (h0 : (g667 (M := M) a0 a1 a2 a3 )) : (g668 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  let e3  : Prop := (t3 ((show Prop from (t16 (M := M) (a1) (a3)))) ((show Prop from (t16 (M := M) (a2) (a3)))))
  have v0 : ((show Prop from (t0 (e0) (e3)))) := p572 (M := M) (a3) (a1) (a2)
  have v1 : ((show Prop from (t0 (a0) (e3)))) := p10 (a0) (e0) (e3) (v0) (h0)
  exact v1
-- Actual MMB 575 eleq2d
theorem p575 (a0 : Prop) (a1 : M) (a2 : (M → Prop)) (a3 : (M → Prop)) (h0 : (g669 (M := M) a0 a1 a2 a3 )) : (g670 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t17 (M := M) (a2) (a3))
  let e3  : Prop := (t3 ((show Prop from (t16 (M := M) (a1) (a2)))) ((show Prop from (t16 (M := M) (a1) (a3)))))
  have v0 : ((show Prop from (t0 (e0) (e3)))) := p573 (M := M) (a2) (a3) (a1)
  have v1 : ((show Prop from (t0 (a0) (e3)))) := p10 (a0) (e0) (e3) (v0) (h0)
  exact v1
-- Actual MMB 576 eleqd
theorem p576 (a0 : Prop) (a1 : M) (a2 : M) (a3 : (M → Prop)) (a4 : (M → Prop)) (h0 : (g671 (M := M) a0 a1 a2 a3 a4 )) (h1 : (g672 (M := M) a0 a1 a2 a3 a4 )) : (g673 (M := M) a0 a1 a2 a3 a4 ) := by
  let e0  : Prop := (t16 (M := M) (a1) (a3))
  let e1  : Prop := (t16 (M := M) (a2) (a3))
  let e4  : Prop := (t16 (M := M) (a2) (a4))
  have v0 : ((show Prop from (t0 (a0) ((show Prop from (t3 (e0) (e1))))))) := p574 (M := M) (a0) (a1) (a2) (a3) (h0)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t3 (e1) (e4))))))) := p575 (M := M) (a0) (a2) (a3) (a4) (h1)
  have v2 : ((show Prop from (t0 (a0) ((show Prop from (t3 (e0) (e4))))))) := p145 (a0) (e0) (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 577 eqseqd
theorem p577 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : (M → Prop)) (h0 : (g674 (M := M) a0 a1 a2 a3 a4 )) (h1 : (g675 (M := M) a0 a1 a2 a3 a4 )) : (g676 (M := M) a0 a1 a2 a3 a4 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a2))
  let e2 (u0 : M) : Prop := (t3 (e0 u0) (e1 u0))
  let e3 (u0 : M) : Prop := (t0 (a0) (e2 u0))
  let e4 (u0 : M) : Prop := (t16 (M := M) u0 (a3))
  let e5 (u0 : M) : Prop := (t16 (M := M) u0 (a4))
  let e6 (u0 : M) : Prop := (t3 (e4 u0) (e5 u0))
  let e7 (u0 : M) : Prop := (t0 (a0) (e6 u0))
  let e8 (u0 : M) : Prop := (t3 (e0 u0) (e4 u0))
  let e9 (u0 : M) : Prop := (t3 (e1 u0) (e5 u0))
  let e10 (u0 : M) : Prop := (t3 (e8 u0) (e9 u0))
  let e11 (u0 : M) : Prop := (t0 (a0) (e10 u0))
  let e19  : Prop := (t0 (a0) ((show Prop from (t3 ((show Prop from (t17 (M := M) (a1) (a3)))) ((show Prop from (t17 (M := M) (a2) (a4))))))))
  have v0 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p575 (M := M) (a0) z0 (a1) (a2) (h0)
  have v1 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p575 (M := M) (a0) z0 (a3) (a4) (h1)
  have v2 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p233 (a0) (e0 z0) (e1 z0) (e4 z0) (e5 z0) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t0 (a0) ((show Prop from (t3 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e8 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e9 x0_0))))))))))) := p371 (M := M) (a0) (fun w1 : M => (e8 w1)) (fun w1 : M => (e9 w1)) ((fun w1 : M => v2 w1))
  have v4 : (e19) := (show (e19) from v3)
  exact v4
-- Actual MMB 578 eqseq
theorem p579 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (h0 : (g678 (M := M) a0 a1 a2 a3 )) : (g679 (M := M) a0 a1 a2 a3 ) := by
  have v0 : ((show Prop from (t0 (a0) ((show Prop from (t17 (M := M) (a3) (a3))))))) := p562 (M := M) (a0) (a3)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t3 ((show Prop from (t17 (M := M) (a1) (a3)))) ((show Prop from (t17 (M := M) (a2) (a3)))))))))) := p577 (M := M) (a0) (a1) (a2) (a3) (a3) (h0) (v0)
  exact v1
-- Actual MMB 580 eqseq1
theorem p581 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (h0 : (g681 (M := M) a0 a1 a2 a3 )) : (g682 (M := M) a0 a1 a2 a3 ) := by
  have v0 : ((show Prop from (t0 (a0) ((show Prop from (t17 (M := M) (a1) (a1))))))) := p562 (M := M) (a0) (a1)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t3 ((show Prop from (t17 (M := M) (a1) (a2)))) ((show Prop from (t17 (M := M) (a1) (a3)))))))))) := p577 (M := M) (a0) (a1) (a1) (a2) (a3) (v0) (h0)
  exact v1
-- Actual MMB 582 eqseq2
theorem p582 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : (g683 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t17 (M := M) (a1) (a2))
  have v0 : ((show Prop from (t0 (e0) (e0)))) := p8 (e0)
  have v1 : ((show Prop from (t0 (e0) ((show Prop from (t3 ((show Prop from (t17 (M := M) (a0) (a1)))) ((show Prop from (t17 (M := M) (a0) (a2)))))))))) := p581 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 583 abeq
theorem p583 (a1 : M → Prop) (a2 : M → Prop)  : (g684 (M := M) a1 a2 ) := by
  let e0  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (e0))
  let e2 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a1 x0_1)))
  let e3 (u0 : M) : Prop := (t3 (e1 u0) (e2 u0))
  let e4  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a2 x0_0)))
  let e5 (u0 : M) : Prop := (t16 (M := M) u0 (e4))
  let e6 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a2 x0_1)))
  let e7 (u0 : M) : Prop := (t3 (e5 u0) (e6 u0))
  let e8 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0)))
  let e9 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e6 u0)))
  let e10 (u0 : M) : Prop := (t3 (e2 u0) (e6 u0))
  let e11 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e10 u0)))
  let e12 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e13 (u0 : M) (u1 : M) : Prop := (t3 (a1 u1) (e2 u0))
  let e14 (u0 : M) (u1 : M) : Prop := (t0 (e12 u0 u1) (e13 u0 u1))
  let e15 (u0 : M) (u1 : M) : Prop := (t3 (a2 u1) (e6 u0))
  let e16 (u0 : M) (u1 : M) : Prop := (t0 (e12 u0 u1) (e15 u0 u1))
  let e17 (u0 : M) : Prop := (t3 (a1 u0) (a2 u0))
  let e18 (u0 : M) (u1 : M) : Prop := (t3 (e17 u1) (e10 u0))
  let e19 (u0 : M) (u1 : M) : Prop := (t0 (e12 u0 u1) (e18 u0 u1))
  let e20  : Prop := (t8 (M := M) (fun x0_0 : M => (e17 x0_0)))
  let e21 (u0 : M) : Prop := (t0 (e20) (e10 u0))
  let e22 (u0 : M) : Prop := (t3 (e1 u0) (e5 u0))
  let e23 (u0 : M) : Prop := (t0 (e20) (e22 u0))
  let e27  : Prop := (t0 (e20) ((show Prop from (t17 (M := M) (e0) (e4)))))
  have v0 : (∀ z0 : M, (e3 z0)) := fun z0 : M => b552 (M := M) z0 (fun w1 : M => (a1 w1))
  have v1 : (∀ z0 : M, (e7 z0)) := fun z0 : M => b552 (M := M) z0 (fun w1 : M => (a2 w1))
  have v2 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p518 (M := M) z0 (fun w0 : M => (a1 w0))
  have v3 : (∀ z0 : M, (e9 z0)) := fun z0 : M => p518 (M := M) z0 (fun w0 : M => (a2 w0))
  have v4 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p415 (M := M) (fun w0 : M => (e2 z0)) (fun w0 : M => (e6 z0)) (v2 z0) (v3 z0)
  have v5 : (∀ z0 : M, (∀ z1 : M, (e14 z0 z1))) := fun z0 : M => fun z1 : M => p516 (M := M) z0 (fun w0 : M => (a1 w0)) z1
  have v6 : (∀ z0 : M, (∀ z1 : M, (e16 z0 z1))) := fun z0 : M => fun z1 : M => p516 (M := M) z0 (fun w0 : M => (a2 w0)) z1
  have v7 : (∀ z0 : M, (∀ z1 : M, (e19 z0 z1))) := fun z0 : M => fun z1 : M => p233 (e12 z0 z1) (a1 z1) (e2 z0) (a2 z1) (e6 z0) (v5 z0 z1) (v6 z0 z1)
  have v8 : (∀ z0 : M, (e21 z0)) := fun z0 : M => p429 (M := M) z0 (fun w0 : M => (e17 w0)) (fun w0 : M => (e10 z0)) (v4 z0) ((fun w0 : M => v7 z0 w0)) 0
  have v9 : (∀ z0 : M, (e23 z0)) := fun z0 : M => p172 (e20) (e2 z0) (e6 z0) (e1 z0) (e5 z0) (v0 z0) (v1 z0) (v8 z0)
  have v10 : ((show Prop from (t0 (e20) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e22 x0_0)))))))) := p338 (M := M) (e20) (fun w0 : M => (e22 w0)) ((fun w0 : M => v9 w0))
  have v11 : (e27) := (show (e27) from v10)
  exact v11
-- Actual MMB 584 abeqd
theorem p584 (a0 : Prop) (a2 : M → Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (g387 (M := M) a0 a2 a3 z0))) : (g685 (M := M) a0 a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t3 (a2 u0) (a3 u0))
  let e1  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e4  : Prop := (t17 (M := M) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (a3 x0_0))))))
  have v0 : ((show Prop from (t0 (e1) (e4)))) := p583 (M := M) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3 w0))
  have v1 : ((show Prop from (t0 (a0) (e1)))) := p338 (M := M) (a0) (fun w0 : M => (e0 w0)) ((fun w0 : M => h0 w0))
  have v2 : ((show Prop from (t0 (a0) (e4)))) := p10 (a0) (e1) (e4) (v0) (v1)
  exact v2
-- Actual MMB 585 abeqi
theorem p585 (a1 : M → Prop) (a2 : M → Prop) (h0 : (∀ z0 : M, (g379 (M := M) a1 a2 z0))) : (g686 (M := M) a1 a2 ) := by
  let e0  : Prop := (t6)
  let e1 (u0 : M) : Prop := (t3 (a1 u0) (a2 u0))
  let e2 (u0 : M) : Prop := (t0 (e0) (e1 u0))
  let e5  : Prop := (t17 (M := M) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (a1 x0_0))))) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (a2 x0_0))))))
  have v0 : (∀ z0 : M, (e2 z0)) := fun z0 : M => p4 (e0) (e1 z0) (h0 z0)
  have v1 : ((show Prop from (t0 (e0) (e5)))) := p584 (M := M) (e0) (fun w1 : M => (a1 w1)) (fun w1 : M => (a2 w1)) ((fun w1 : M => v0 w1))
  have v2 : (e5) := p318 (e5) (v1)
  exact v2
-- Actual MMB 586 eqri
theorem p586 (a0 : (M → Prop)) (a1 : (M → Prop)) (h0 : (∀ z0 : M, (g687 (M := M) a0 a1 z0))) : (g688 (M := M) a0 a1 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e2 (u0 : M) : Prop := (t3 (e0 u0) (e1 u0))
  let e4  : Prop := (t17 (M := M) (a0) (a1))
  have v0 : ((show Prop from (t8 (M := M) (fun x0_0 : M => (e2 x0_0))))) := b325 (M := M) (fun w0 : M => (e2 w0)) ((fun w0 : M => h0 w0))
  have v1 : (e4) := (show (e4) from v0)
  exact v1
-- Actual MMB 587 eqrd
theorem p587 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : Prop) (h0 : (∀ z0 : M, (g689 (M := M) a0 a1 a2 z0))) : (g690 (M := M) a0 a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e2 (u0 : M) : Prop := (t3 (e0 u0) (e1 u0))
  let e6  : Prop := (t0 (a2) ((show Prop from (t17 (M := M) (a0) (a1)))))
  have v0 : ((show Prop from (t0 (a2) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e2 x0_0)))))))) := p338 (M := M) (a2) (fun w0 : M => (e2 w0)) ((fun w0 : M => h0 w0))
  have v1 : (e6) := (show (e6) from v0)
  exact v1
-- Actual MMB 588 cbvabh
theorem p588 (a2 : M → M → Prop) (a3 : M → M → Prop) (h0 : (∀ z0 : M, (g529 (M := M) a2 a3 z0))) (h1 : (∀ z0 : M, (g530 (M := M) a2 a3 z0))) (h2 : (∀ z0 : M, (∀ z1 : M, (g531 (M := M) a2 a3 z0 z1)))) : (∀ z0 : M, (∀ z1 : M, (g691 (M := M) a2 a3 z0 z1))) := by
  let e0 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a2 x0_0 u0)))
  let e1 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (e0 u1))
  let e2 (u0 : M) (u1 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a2 x0_1 u1)))
  let e3 (u0 : M) (u1 : M) : Prop := (t3 (e1 u0 u1) (e2 u0 u1))
  let e4 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a3 u0 x0_0)))
  let e5 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (e4 u1))
  let e6 (u0 : M) (u1 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a3 u1 x0_1)))
  let e7 (u0 : M) (u1 : M) : Prop := (t3 (e5 u0 u1) (e6 u0 u1))
  let e8 (u0 : M) (u1 : M) (u2 : M) : Prop := (t3 (e2 u0 u2) (e6 u0 u1))
  let e9 (u0 : M) (u1 : M) (u2 : M) : Prop := (t3 (e1 u0 u2) (e5 u0 u1))
  let e10 (u0 : M) (u1 : M) : Prop := (t17 (M := M) (e0 u1) (e4 u0))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e3 z0 z1))) := fun z0 : M => fun z1 : M => b552 (M := M) z0 (fun w1 : M => (a2 w1 z1))
  have v1 : (∀ z0 : M, (∀ z1 : M, (e7 z0 z1))) := fun z0 : M => fun z1 : M => b552 (M := M) z0 (fun w1 : M => (a3 z1 w1))
  have v2 : (∀ z0 : M, (∀ z1 : M, (∀ z2 : M, (e8 z0 z1 z2)))) := fun z0 : M => fun z1 : M => fun z2 : M => p539 (M := M) z0 (fun w0 : M => (fun w1 : M => (a2 w0 w1))) (fun w0 : M => (fun w1 : M => (a3 w0 w1))) ((fun w0 : M => h0 w0)) ((fun w1 : M => h1 w1)) ((fun w0 : M => (fun w1 : M => h2 w0 w1))) z1 z2
  have v3 : (∀ z0 : M, (∀ z1 : M, (∀ z2 : M, (e9 z0 z1 z2)))) := fun z0 : M => fun z1 : M => fun z2 : M => p174 (e2 z0 z2) (e6 z0 z1) (e1 z0 z2) (e5 z0 z1) (v0 z0 z2) (v1 z0 z1) (v2 z0 z1 z2)
  have v4 : (∀ z0 : M, (∀ z1 : M, (e10 z0 z1))) := fun z0 : M => fun z1 : M => p586 (M := M) (e0 z1) (e4 z0) ((fun w2 : M => v3 w2 z0 z1))
  exact v4
-- Actual MMB 589 cbvab
theorem p589 (a2 : M → Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (∀ z1 : M, (g533 (M := M) a2 a3 z0 z1)))) : (g692 (M := M) a2 a3 ) := by
  let e0 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a2 u0)))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a3 u0)))
  have v0 : (∀ z0 : M, (e0 z0)) := fun z0 : M => p405 (M := M) (a2 z0)
  have v1 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p405 (M := M) (a3 z0)
  have v2 : ((show Prop from (t17 (M := M) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (a2 x0_0))))) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (a3 x0_0)))))))) := p588 (M := M) (fun w0 : M => (fun w1 : M => (a2 w0))) (fun w0 : M => (fun w1 : M => (a3 w1))) ((fun w0 : M => v0 w0)) ((fun w1 : M => v1 w1)) ((fun w0 : M => (fun w1 : M => h0 w0 w1))) 0 0
  exact v2
-- Actual MMB 590 cbvabs
theorem p592 (a1 : M → M) (a2 : M → Prop)  : (∀ z0 : M, (g695 (M := M) a1 a2 z0)) := by
  let e0  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a2 x0_0)))
  let e1 (u0 : M) : Prop := (t16 (M := M) (a1 u0) (e0))
  let e2 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a2 x0_1)))
  let e3 (u0 : M) : Prop := (t14 (M := M) (a1 u0) (fun x0_1 : M => (e2 x0_1)))
  let e4 (u0 : M) : Prop := (t14 (M := M) (a1 u0) (fun x0_1 : M => (a2 x0_1)))
  let e5 (u0 : M) : Prop := (t3 (e1 u0) (e3 u0))
  let e6 (u0 : M) : Prop := (t3 (e3 u0) (e4 u0))
  let e7 (u0 : M) : Prop := (t3 (e1 u0) (e4 u0))
  let e8 (u0 : M) : Prop := (t0 (e6 u0) (e7 u0))
  let e9 (u0 : M) : Prop := (t0 (e5 u0) (e8 u0))
  let e10  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e11 (u0 : M) : Prop := (t16 (M := M) (a1 u0) (e10))
  let e12 (u0 : M) : Prop := (t3 (e1 u0) (e11 u0))
  let e13 (u0 : M) : Prop := (t3 (e11 u0) (e3 u0))
  let e14 (u0 : M) : Prop := (t0 (e13 u0) (e5 u0))
  let e15 (u0 : M) : Prop := (t0 (e12 u0) (e14 u0))
  let e16  : Prop := (t17 (M := M) (e0) (e10))
  let e17 (u0 : M) : Prop := (t0 (e16) (e12 u0))
  let e18 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a2 u0)))
  let e19 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0)))
  let e20 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e21 (u0 : M) (u1 : M) : Prop := (t3 (a2 u1) (e2 u0))
  let e22 (u0 : M) (u1 : M) : Prop := (t0 (e20 u0 u1) (e21 u0 u1))
  have v0 : (∀ z0 : M, (e9 z0)) := fun z0 : M => p149 (e1 z0) (e3 z0) (e4 z0)
  have v1 : (∀ z0 : M, (e15 z0)) := fun z0 : M => p149 (e1 z0) (e11 z0) (e3 z0)
  have v2 : (∀ z0 : M, (e17 z0)) := fun z0 : M => p573 (M := M) (e0) (e10) (a1 z0)
  have v3 : (∀ z0 : M, (e18 z0)) := fun z0 : M => p405 (M := M) (a2 z0)
  have v4 : (∀ z0 : M, (e19 z0)) := fun z0 : M => p518 (M := M) z0 (fun w0 : M => (a2 w0))
  have v5 : (∀ z0 : M, (∀ z1 : M, (e22 z0 z1))) := fun z0 : M => fun z1 : M => p516 (M := M) z0 (fun w0 : M => (a2 w0)) z1
  have v6 : (e16) := p588 (M := M) (fun w0 : M => (fun w1 : M => (a2 w0))) (fun w0 : M => (fun w1 : M => (e2 w1))) ((fun w0 : M => v3 w0)) ((fun w1 : M => v4 w1)) ((fun w0 : M => (fun w1 : M => v5 w1 w0))) 0 0
  have v7 : (∀ z0 : M, (e12 z0)) := fun z0 : M => b3 (e16) (e12 z0) (v2 z0) (v6)
  have v8 : (∀ z0 : M, (e14 z0)) := fun z0 : M => b3 (e12 z0) (e14 z0) (v1 z0) (v7 z0)
  have v9 : (∀ z0 : M, (e13 z0)) := fun z0 : M => b552 (M := M) (a1 z0) (fun w1 : M => (e2 w1))
  have v10 : (∀ z0 : M, (e5 z0)) := fun z0 : M => b3 (e13 z0) (e5 z0) (v8 z0) (v9 z0)
  have v11 : (∀ z0 : M, (e8 z0)) := fun z0 : M => b3 (e5 z0) (e8 z0) (v0 z0) (v10 z0)
  have v12 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p532 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (a2 w0)) z0
  have v13 : (∀ z0 : M, (e7 z0)) := fun z0 : M => b3 (e6 z0) (e7 z0) (v11 z0) (v12 z0)
  exact v13
-- Actual MMB 593 elabe
theorem p593 (a1 : M) (a2 : M → Prop) (a3 : Prop) (h0 : (∀ z0 : M, (g468 (M := M) a1 a2 a3 z0))) : (g696 (M := M) a1 a2 a3 ) := by
  let e1  : Prop := (t16 (M := M) (a1) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (a2 x0_0))))))
  let e2  : Prop := (t14 (M := M) (a1) (fun x0_1 : M => (a2 x0_1)))
  let e3  : Prop := (t3 (e1) (e2))
  let e4  : Prop := (t3 (e2) (a3))
  let e5  : Prop := (t3 (e1) (a3))
  let e6  : Prop := (t0 (e4) (e5))
  have v0 : ((show Prop from (t0 (e3) (e6)))) := p149 (e1) (e2) (a3)
  have v1 : (e3) := p592 (M := M) (fun w0 : M => (a1)) (fun w0 : M => (a2 w0)) 0
  have v2 : (e6) := b3 (e3) (e6) (v0) (v1)
  have v3 : (e4) := p528 (M := M) (a1) (fun w0 : M => (a2 w0)) (a3) ((fun w0 : M => h0 w0))
  have v4 : (e5) := b3 (e4) (e5) (v2) (v3)
  exact v4
-- Actual MMB 594 elabed
theorem p594 (a0 : Prop) (a2 : M) (a3 : M → Prop) (a4 : Prop) (h0 : (∀ z0 : M, (g602 (M := M) a0 a2 a3 a4 z0))) : (g697 (M := M) a0 a2 a3 a4 ) := by
  let e1  : Prop := (t16 (M := M) (a2) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (a3 x0_0))))))
  let e2  : Prop := (t14 (M := M) (a2) (fun x0_1 : M => (a3 x0_1)))
  have v0 : ((show Prop from (t3 (e1) (e2)))) := p592 (M := M) (fun w0 : M => (a2)) (fun w0 : M => (a3 w0)) 0
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t3 (e2) (a4))))))) := p529 (M := M) (a0) (a2) (fun w1 : M => (a3 w1)) (a4) ((fun w1 : M => h0 w1))
  have v2 : ((show Prop from (t0 (a0) ((show Prop from (t3 (e1) (a4))))))) := p157 (a0) (e1) (e2) (a4) (v0) (v1)
  exact v2
-- Actual MMB 595 ssabed
theorem p598 (a1 : M → Prop)  : (∀ z0 : M, (g704 (M := M) a1 z0)) := by
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (a1 x0_0))))))
  let e2 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a1 x0_1)))
  let e3 (u0 : M) : Prop := (t3 (e1 u0) (e2 u0))
  let e4 (u0 : M) : Prop := (t3 (e2 u0) (a1 u0))
  let e5 (u0 : M) : Prop := (t3 (e1 u0) (a1 u0))
  let e6 (u0 : M) : Prop := (t0 (e4 u0) (e5 u0))
  let e7 (u0 : M) : Prop := (t0 (e3 u0) (e6 u0))
  have v0 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p149 (e1 z0) (e2 z0) (a1 z0)
  have v1 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p592 (M := M) (fun w0 : M => w0) (fun w0 : M => (a1 w0)) z0
  have v2 : (∀ z0 : M, (e6 z0)) := fun z0 : M => b3 (e3 z0) (e6 z0) (v0 z0) (v1 z0)
  have v3 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p533 (M := M) (fun w0 : M => (a1 w0)) z0
  have v4 : (∀ z0 : M, (e5 z0)) := fun z0 : M => b3 (e4 z0) (e5 z0) (v2 z0) (v3 z0)
  exact v4
-- Actual MMB 599 abid2
theorem p600 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : (M → Prop)) (h0 : (g674 (M := M) a0 a1 a2 a3 a4 )) (h1 : (g675 (M := M) a0 a1 a2 a3 a4 )) : (g706 (M := M) a0 a1 a2 a3 a4 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a2))
  let e2 (u0 : M) : Prop := (t3 (e0 u0) (e1 u0))
  let e3 (u0 : M) : Prop := (t0 (a0) (e2 u0))
  let e4 (u0 : M) : Prop := (t16 (M := M) u0 (a3))
  let e5 (u0 : M) : Prop := (t16 (M := M) u0 (a4))
  let e6 (u0 : M) : Prop := (t3 (e4 u0) (e5 u0))
  let e7 (u0 : M) : Prop := (t0 (a0) (e6 u0))
  let e8 (u0 : M) : Prop := (t0 (e0 u0) (e4 u0))
  let e9 (u0 : M) : Prop := (t0 (e1 u0) (e5 u0))
  let e10 (u0 : M) : Prop := (t3 (e8 u0) (e9 u0))
  let e11 (u0 : M) : Prop := (t0 (a0) (e10 u0))
  let e19  : Prop := (t0 (a0) ((show Prop from (t3 ((show Prop from (t18 (M := M) (a1) (a3)))) ((show Prop from (t18 (M := M) (a2) (a4))))))))
  have v0 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p575 (M := M) (a0) z0 (a1) (a2) (h0)
  have v1 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p575 (M := M) (a0) z0 (a3) (a4) (h1)
  have v2 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p188 (a0) (e0 z0) (e1 z0) (e4 z0) (e5 z0) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t0 (a0) ((show Prop from (t3 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e8 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e9 x0_0))))))))))) := p371 (M := M) (a0) (fun w1 : M => (e8 w1)) (fun w1 : M => (e9 w1)) ((fun w1 : M => v2 w1))
  have v4 : (e19) := (show (e19) from v3)
  exact v4
-- Actual MMB 601 sseq
theorem p602 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (h0 : (g678 (M := M) a0 a1 a2 a3 )) : (g708 (M := M) a0 a1 a2 a3 ) := by
  have v0 : ((show Prop from (t0 (a0) ((show Prop from (t17 (M := M) (a3) (a3))))))) := p562 (M := M) (a0) (a3)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t3 ((show Prop from (t18 (M := M) (a1) (a3)))) ((show Prop from (t18 (M := M) (a2) (a3)))))))))) := p600 (M := M) (a0) (a1) (a2) (a3) (a3) (h0) (v0)
  exact v1
-- Actual MMB 603 sseq1
theorem p603 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : (g709 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t17 (M := M) (a0) (a1))
  have v0 : ((show Prop from (t0 (e0) (e0)))) := p8 (e0)
  have v1 : ((show Prop from (t0 (e0) ((show Prop from (t3 ((show Prop from (t18 (M := M) (a0) (a2)))) ((show Prop from (t18 (M := M) (a1) (a2)))))))))) := p602 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 604 sseq2d
theorem p604 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (h0 : (g681 (M := M) a0 a1 a2 a3 )) : (g710 (M := M) a0 a1 a2 a3 ) := by
  have v0 : ((show Prop from (t0 (a0) ((show Prop from (t17 (M := M) (a1) (a1))))))) := p562 (M := M) (a0) (a1)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t3 ((show Prop from (t18 (M := M) (a1) (a2)))) ((show Prop from (t18 (M := M) (a1) (a3)))))))))) := p600 (M := M) (a0) (a1) (a1) (a2) (a3) (v0) (h0)
  exact v1
-- Actual MMB 605 sseq2
theorem p605 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : (g711 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t17 (M := M) (a1) (a2))
  have v0 : ((show Prop from (t0 (e0) (e0)))) := p8 (e0)
  have v1 : ((show Prop from (t0 (e0) ((show Prop from (t3 ((show Prop from (t18 (M := M) (a0) (a1)))) ((show Prop from (t18 (M := M) (a0) (a2)))))))))) := p604 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 606 dfss
theorem p607 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : M)  : (g713 (M := M) a0 a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e2  : Prop := (t16 (M := M) (a2) (a0))
  let e3 (u0 : M) : Prop := (t3 (e1 u0) (e2))
  let e4 (u0 : M) : Prop := (t0 (e0 u0) (e3 u0))
  let e5 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e6  : Prop := (t16 (M := M) (a2) (a1))
  let e7 (u0 : M) : Prop := (t3 (e5 u0) (e6))
  let e8 (u0 : M) : Prop := (t0 (e0 u0) (e7 u0))
  let e9 (u0 : M) : Prop := (t0 (e1 u0) (e5 u0))
  let e10  : Prop := (t0 (e2) (e6))
  let e11 (u0 : M) : Prop := (t3 (e9 u0) (e10))
  let e12 (u0 : M) : Prop := (t0 (e0 u0) (e11 u0))
  let e16  : Prop := (t0 ((show Prop from (t18 (M := M) (a0) (a1)))) (e10))
  have v0 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p572 (M := M) (a0) z0 (a2)
  have v1 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p572 (M := M) (a1) z0 (a2)
  have v2 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p188 (e0 z0) (e1 z0) (e2) (e5 z0) (e6) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e9 x0_0))))) (e10)))) := p440 (M := M) (a2) (fun w0 : M => (e9 w0)) (e10) ((fun w0 : M => v2 w0))
  have v4 : (e16) := (show (e16) from v3)
  exact v4
-- Actual MMB 608 sseld
theorem p608 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : Prop) (a3 : M) (h0 : (g714 (M := M) a0 a1 a2 a3 )) (h1 : (g715 (M := M) a0 a1 a2 a3 )) : (g716 (M := M) a0 a1 a2 a3 ) := by
  let e0  : Prop := (t18 (M := M) (a0) (a1))
  let e1  : Prop := (t16 (M := M) (a3) (a0))
  let e2  : Prop := (t16 (M := M) (a3) (a1))
  have v0 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e1) (e2))))))) := p607 (M := M) (a0) (a1) (a3)
  have v1 : ((show Prop from (t0 (a2) (e2)))) := p15 (a2) (e0) (e1) (e2) (v0) (h0) (h1)
  exact v1
-- Actual MMB 609 ssid
theorem p609 (a0 : (M → Prop))  : (g717 (M := M) a0 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e1 (u0 : M) : Prop := (t0 (e0 u0) (e0 u0))
  let e3  : Prop := (t18 (M := M) (a0) (a0))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p8 (e0 z0)
  have v1 : ((show Prop from (t8 (M := M) (fun x0_0 : M => (e1 x0_0))))) := b325 (M := M) (fun w0 : M => (e1 w0)) ((fun w0 : M => v0 w0))
  have v2 : (e3) := (show (e3) from v1)
  exact v2
-- Actual MMB 610 sstr
theorem p610 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : (g718 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t18 (M := M) (a0) (a1))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e2 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e3 (u0 : M) : Prop := (t0 (e1 u0) (e2 u0))
  let e4 (u0 : M) : Prop := (t0 (e0) (e3 u0))
  let e5  : Prop := (t18 (M := M) (a1) (a2))
  let e6  : Prop := (t2 (e0) (e5))
  let e7 (u0 : M) : Prop := (t0 (e6) (e3 u0))
  let e8 (u0 : M) : Prop := (t16 (M := M) u0 (a2))
  let e9 (u0 : M) : Prop := (t0 (e2 u0) (e8 u0))
  let e10 (u0 : M) : Prop := (t0 (e5) (e9 u0))
  let e11 (u0 : M) : Prop := (t0 (e6) (e9 u0))
  let e12 (u0 : M) : Prop := (t0 (e1 u0) (e8 u0))
  let e13 (u0 : M) : Prop := (t0 (e6) (e12 u0))
  let e16  : Prop := (t18 (M := M) (a0) (a2))
  let e17  : Prop := (t0 (e6) (e16))
  have v0 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p607 (M := M) (a0) (a1) z0
  have v1 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p62 (e0) (e5) (e3 z0) (v0 z0)
  have v2 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p607 (M := M) (a1) (a2) z0
  have v3 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p63 (e0) (e5) (e9 z0) (v2 z0)
  have v4 : (∀ z0 : M, (e13 z0)) := fun z0 : M => p16 (e6) (e1 z0) (e2 z0) (e8 z0) (v1 z0) (v3 z0)
  have v5 : ((show Prop from (t0 (e6) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e12 x0_0)))))))) := p338 (M := M) (e6) (fun w0 : M => (e12 w0)) ((fun w0 : M => v4 w0))
  have v6 : (e17) := (show (e17) from v5)
  have v7 : ((show Prop from (t0 (e0) ((show Prop from (t0 (e5) (e16))))))) := p84 (e0) (e5) (e16) (v6)
  exact v7
-- Actual MMB 611 eqss
theorem p611 (a0 : (M → Prop)) (a1 : (M → Prop))  : (g719 (M := M) a0 a1 ) := by
  let e0  : Prop := (t18 (M := M) (a0) (a0))
  let e1  : Prop := (t17 (M := M) (a0) (a1))
  let e2  : Prop := (t18 (M := M) (a0) (a1))
  have v0 : (e0) := p609 (M := M) (a0)
  have v1 : ((show Prop from (t0 (e1) ((show Prop from (t3 (e0) (e2))))))) := p605 (M := M) (a0) (a0) (a1)
  have v2 : ((show Prop from (t0 (e1) (e2)))) := p121 (e1) (e0) (e2) (v0) (v1)
  exact v2
-- Actual MMB 612 eqssr
theorem p612 (a0 : (M → Prop)) (a1 : (M → Prop))  : (g720 (M := M) a0 a1 ) := by
  let e0  : Prop := (t18 (M := M) (a0) (a0))
  let e1  : Prop := (t17 (M := M) (a0) (a1))
  let e2  : Prop := (t18 (M := M) (a1) (a0))
  have v0 : (e0) := p609 (M := M) (a0)
  have v1 : ((show Prop from (t0 (e1) ((show Prop from (t3 (e0) (e2))))))) := p603 (M := M) (a0) (a1) (a0)
  have v2 : ((show Prop from (t0 (e1) (e2)))) := p121 (e1) (e0) (e2) (v0) (v1)
  exact v2
-- Actual MMB 613 ssasym
theorem p613 (a0 : (M → Prop)) (a1 : (M → Prop))  : (g721 (M := M) a0 a1 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e2 (u0 : M) : Prop := (t0 (e0 u0) (e1 u0))
  let e3 (u0 : M) : Prop := (t0 (e1 u0) (e0 u0))
  let e4 (u0 : M) : Prop := (t2 (e2 u0) (e3 u0))
  let e5 (u0 : M) : Prop := (t0 (e3 u0) (e4 u0))
  let e6 (u0 : M) : Prop := (t0 (e2 u0) (e5 u0))
  let e7 (u0 : M) : Prop := (t3 (e0 u0) (e1 u0))
  let e8 (u0 : M) : Prop := (t0 (e3 u0) (e7 u0))
  let e9 (u0 : M) : Prop := (t0 (e2 u0) (e8 u0))
  let e19  : Prop := (t0 ((show Prop from (t18 (M := M) (a0) (a1)))) ((show Prop from (t0 ((show Prop from (t18 (M := M) (a1) (a0)))) ((show Prop from (t17 (M := M) (a0) (a1))))))))
  have v0 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p57 _ _
  have v1 : (∀ z0 : M, (e9 z0)) := (show (∀ z0 : M, (e9 z0)) from v0)
  have v2 : ((show Prop from (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e2 x0_0))))) ((show Prop from (t0 ((show Prop from (t8 (M := M) (fun x0_0 : M => (e3 x0_0))))) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e7 x0_0))))))))))) := p370 (M := M) (fun w0 : M => (e2 w0)) (fun w0 : M => (e3 w0)) (fun w0 : M => (e7 w0)) ((fun w0 : M => v1 w0))
  have v3 : (e19) := (show (e19) from v2)
  exact v3
-- Actual MMB 614 ssasymd
theorem p616 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : (M → Prop)) (h0 : (g674 (M := M) a0 a1 a2 a3 a4 )) (h1 : (g675 (M := M) a0 a1 a2 a3 a4 )) : (g725 (M := M) a0 a1 a2 a3 a4 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a2))
  let e2 (u0 : M) : Prop := (t3 (e0 u0) (e1 u0))
  let e3 (u0 : M) : Prop := (t0 (a0) (e2 u0))
  let e4 (u0 : M) : Prop := (t16 (M := M) u0 (a3))
  let e5 (u0 : M) : Prop := (t16 (M := M) u0 (a4))
  let e6 (u0 : M) : Prop := (t3 (e4 u0) (e5 u0))
  let e7 (u0 : M) : Prop := (t0 (a0) (e6 u0))
  let e8 (u0 : M) : Prop := (t2 (e0 u0) (e4 u0))
  let e9 (u0 : M) : Prop := (t2 (e1 u0) (e5 u0))
  let e10 (u0 : M) : Prop := (t3 (e8 u0) (e9 u0))
  let e11 (u0 : M) : Prop := (t0 (a0) (e10 u0))
  let e19  : Prop := (t0 (a0) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t19 (M := M) (a1) (a3)))) ((show (M → Prop) from (t19 (M := M) (a2) (a4))))))))
  have v0 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p575 (M := M) (a0) z0 (a1) (a2) (h0)
  have v1 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p575 (M := M) (a0) z0 (a3) (a4) (h1)
  have v2 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p196 (a0) (e0 z0) (e1 z0) (e4 z0) (e5 z0) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t0 (a0) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e8 x0_0))))) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e9 x0_0))))))))))) := p584 (M := M) (a0) (fun w1 : M => (e8 w1)) (fun w1 : M => (e9 w1)) ((fun w1 : M => v2 w1))
  have v4 : (e19) := (show (e19) from v3)
  exact v4
-- Actual MMB 617 ineq
theorem p618 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (h0 : (g678 (M := M) a0 a1 a2 a3 )) : (g727 (M := M) a0 a1 a2 a3 ) := by
  have v0 : ((show Prop from (t0 (a0) ((show Prop from (t17 (M := M) (a3) (a3))))))) := p562 (M := M) (a0) (a3)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t19 (M := M) (a1) (a3)))) ((show (M → Prop) from (t19 (M := M) (a2) (a3)))))))))) := p616 (M := M) (a0) (a1) (a2) (a3) (a3) (h0) (v0)
  exact v1
-- Actual MMB 619 ineq1
theorem p619 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : (g728 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t17 (M := M) (a0) (a1))
  have v0 : ((show Prop from (t0 (e0) (e0)))) := p8 (e0)
  have v1 : ((show Prop from (t0 (e0) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t19 (M := M) (a0) (a2)))) ((show (M → Prop) from (t19 (M := M) (a1) (a2)))))))))) := p618 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 620 ineq2d
theorem p622 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : M)  : (g731 (M := M) a0 a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e2  : Prop := (t16 (M := M) (a2) (a0))
  let e3 (u0 : M) : Prop := (t3 (e1 u0) (e2))
  let e4 (u0 : M) : Prop := (t0 (e0 u0) (e3 u0))
  let e5 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e6  : Prop := (t16 (M := M) (a2) (a1))
  let e7 (u0 : M) : Prop := (t3 (e5 u0) (e6))
  let e8 (u0 : M) : Prop := (t0 (e0 u0) (e7 u0))
  let e9 (u0 : M) : Prop := (t2 (e1 u0) (e5 u0))
  let e10  : Prop := (t2 (e2) (e6))
  let e11 (u0 : M) : Prop := (t3 (e9 u0) (e10))
  let e12 (u0 : M) : Prop := (t0 (e0 u0) (e11 u0))
  let e18  : Prop := (t3 ((show Prop from (t16 (M := M) (a2) ((show (M → Prop) from (t19 (M := M) (a0) (a1))))))) (e10))
  have v0 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p572 (M := M) (a0) z0 (a2)
  have v1 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p572 (M := M) (a1) z0 (a2)
  have v2 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p196 (e0 z0) (e1 z0) (e2) (e5 z0) (e6) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t3 ((show Prop from (t16 (M := M) (a2) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e9 x0_0)))))))) (e10)))) := p593 (M := M) (a2) (fun w0 : M => (e9 w0)) (e10) ((fun w0 : M => v2 w0))
  have v4 : (e18) := (show (e18) from v3)
  exact v4
-- Actual MMB 623 incom
theorem p625 (a0 : (M → Prop)) (a1 : (M → Prop))  : (g734 (M := M) a0 a1 ) := by
  let e0  : (M → Prop) := (t19 (M := M) (a0) (a1))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (e0))
  let e2 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e3 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e4 (u0 : M) : Prop := (t2 (e2 u0) (e3 u0))
  let e5 (u0 : M) : Prop := (t3 (e1 u0) (e4 u0))
  let e6 (u0 : M) : Prop := (t0 (e4 u0) (e2 u0))
  let e7 (u0 : M) : Prop := (t0 (e1 u0) (e2 u0))
  let e9  : Prop := (t18 (M := M) (e0) (a0))
  have v0 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p622 (M := M) (a0) (a1) z0
  have v1 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p53 (e2 z0) (e3 z0)
  have v2 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p155 (e1 z0) (e4 z0) (e2 z0) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t8 (M := M) (fun x0_0 : M => (e7 x0_0))))) := b325 (M := M) (fun w0 : M => (e7 w0)) ((fun w0 : M => v2 w0))
  have v4 : (e9) := (show (e9) from v3)
  exact v4
-- Actual MMB 626 inss2
theorem p632 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (a4 : (M → Prop)) (h0 : (g674 (M := M) a0 a1 a2 a3 a4 )) (h1 : (g675 (M := M) a0 a1 a2 a3 a4 )) : (g741 (M := M) a0 a1 a2 a3 a4 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a2))
  let e2 (u0 : M) : Prop := (t3 (e0 u0) (e1 u0))
  let e3 (u0 : M) : Prop := (t0 (a0) (e2 u0))
  let e4 (u0 : M) : Prop := (t16 (M := M) u0 (a3))
  let e5 (u0 : M) : Prop := (t16 (M := M) u0 (a4))
  let e6 (u0 : M) : Prop := (t3 (e4 u0) (e5 u0))
  let e7 (u0 : M) : Prop := (t0 (a0) (e6 u0))
  let e8 (u0 : M) : Prop := (t4 (e0 u0) (e4 u0))
  let e9 (u0 : M) : Prop := (t4 (e1 u0) (e5 u0))
  let e10 (u0 : M) : Prop := (t3 (e8 u0) (e9 u0))
  let e11 (u0 : M) : Prop := (t0 (a0) (e10 u0))
  let e19  : Prop := (t0 (a0) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t20 (M := M) (a1) (a3)))) ((show (M → Prop) from (t20 (M := M) (a2) (a4))))))))
  have v0 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p575 (M := M) (a0) z0 (a1) (a2) (h0)
  have v1 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p575 (M := M) (a0) z0 (a3) (a4) (h1)
  have v2 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p243 (a0) (e0 z0) (e1 z0) (e4 z0) (e5 z0) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t0 (a0) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e8 x0_0))))) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e9 x0_0))))))))))) := p584 (M := M) (a0) (fun w1 : M => (e8 w1)) (fun w1 : M => (e9 w1)) ((fun w1 : M => v2 w1))
  have v4 : (e19) := (show (e19) from v3)
  exact v4
-- Actual MMB 633 uneq
theorem p634 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : (M → Prop)) (h0 : (g678 (M := M) a0 a1 a2 a3 )) : (g743 (M := M) a0 a1 a2 a3 ) := by
  have v0 : ((show Prop from (t0 (a0) ((show Prop from (t17 (M := M) (a3) (a3))))))) := p562 (M := M) (a0) (a3)
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t20 (M := M) (a1) (a3)))) ((show (M → Prop) from (t20 (M := M) (a2) (a3)))))))))) := p632 (M := M) (a0) (a1) (a2) (a3) (a3) (h0) (v0)
  exact v1
-- Actual MMB 635 uneq1
theorem p635 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : (M → Prop))  : (g744 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t17 (M := M) (a0) (a1))
  have v0 : ((show Prop from (t0 (e0) (e0)))) := p8 (e0)
  have v1 : ((show Prop from (t0 (e0) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t20 (M := M) (a0) (a2)))) ((show (M → Prop) from (t20 (M := M) (a1) (a2)))))))))) := p634 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 636 uneq2d
theorem p638 (a0 : (M → Prop)) (a1 : (M → Prop)) (a2 : M)  : (g747 (M := M) a0 a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e2  : Prop := (t16 (M := M) (a2) (a0))
  let e3 (u0 : M) : Prop := (t3 (e1 u0) (e2))
  let e4 (u0 : M) : Prop := (t0 (e0 u0) (e3 u0))
  let e5 (u0 : M) : Prop := (t16 (M := M) u0 (a1))
  let e6  : Prop := (t16 (M := M) (a2) (a1))
  let e7 (u0 : M) : Prop := (t3 (e5 u0) (e6))
  let e8 (u0 : M) : Prop := (t0 (e0 u0) (e7 u0))
  let e9 (u0 : M) : Prop := (t4 (e1 u0) (e5 u0))
  let e10  : Prop := (t4 (e2) (e6))
  let e11 (u0 : M) : Prop := (t3 (e9 u0) (e10))
  let e12 (u0 : M) : Prop := (t0 (e0 u0) (e11 u0))
  let e18  : Prop := (t3 ((show Prop from (t16 (M := M) (a2) ((show (M → Prop) from (t20 (M := M) (a0) (a1))))))) (e10))
  have v0 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p572 (M := M) (a0) z0 (a2)
  have v1 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p572 (M := M) (a1) z0 (a2)
  have v2 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p243 (e0 z0) (e1 z0) (e2) (e5 z0) (e6) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t3 ((show Prop from (t16 (M := M) (a2) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e9 x0_0)))))))) (e10)))) := p593 (M := M) (a2) (fun w0 : M => (e9 w0)) (e10) ((fun w0 : M => v2 w0))
  have v4 : (e18) := (show (e18) from v3)
  exact v4
-- Actual MMB 639 uncom
theorem p663 (a0 : M)  : (g773 (M := M) a0 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a0))
  let e1  : Prop := (t6)
  let e3 (u0 : M) : Prop := (t0 (e0 u0) ((show Prop from (t3 (e1) (e1)))))
  let e8  : Prop := (t16 (M := M) (a0) ((show (M → Prop) from (t22 (M := M)))))
  let e9  : Prop := (t3 (e8) (e1))
  have v0 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p116 (e0 z0) (e1)
  have v1 : ((show Prop from (t3 ((show Prop from (t16 (M := M) (a0) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e1)))))))) (e1)))) := p593 (M := M) (a0) (fun w0 : M => (e1)) (e1) ((fun w0 : M => v0 w0))
  have v2 : (e9) := (show (e9) from v1)
  have v3 : (e1) := b317
  have v4 : (e8) := p118 (e1) (e8) (v2) (v3)
  exact v4
-- Actual MMB 664 inv1
theorem p664 (a0 : (M → Prop))  : (g774 (M := M) a0 ) := by
  let e0  : (M → Prop) := (t22 (M := M))
  let e1  : (M → Prop) := (t19 (M := M) (e0) (a0))
  let e2 (u0 : M) : Prop := (t16 (M := M) u0 (e1))
  let e3 (u0 : M) : Prop := (t16 (M := M) u0 (e0))
  let e4 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e5 (u0 : M) : Prop := (t2 (e3 u0) (e4 u0))
  let e6 (u0 : M) : Prop := (t3 (e2 u0) (e5 u0))
  let e7 (u0 : M) : Prop := (t3 (e5 u0) (e4 u0))
  let e8 (u0 : M) : Prop := (t3 (e2 u0) (e4 u0))
  let e9 (u0 : M) : Prop := (t0 (e7 u0) (e8 u0))
  let e10 (u0 : M) : Prop := (t0 (e6 u0) (e9 u0))
  let e11 (u0 : M) : Prop := (t0 (e3 u0) (e7 u0))
  have v0 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p149 (e2 z0) (e5 z0) (e4 z0)
  have v1 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p622 (M := M) (e0) (a0) z0
  have v2 : (∀ z0 : M, (e9 z0)) := fun z0 : M => b3 (e6 z0) (e9 z0) (v0 z0) (v1 z0)
  have v3 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p181 (e3 z0) (e4 z0)
  have v4 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p663 (M := M) z0
  have v5 : (∀ z0 : M, (e7 z0)) := fun z0 : M => b3 (e3 z0) (e7 z0) (v3 z0) (v4 z0)
  have v6 : (∀ z0 : M, (e8 z0)) := fun z0 : M => b3 (e7 z0) (e8 z0) (v2 z0) (v5 z0)
  have v7 : ((show Prop from (t17 (M := M) (e1) (a0)))) := p586 (M := M) (e1) (a0) ((fun w2 : M => v6 w2))
  exact v7
-- Actual MMB 665 inv2
theorem p673 (a0 : (M → Prop))  : (g785 (M := M) a0 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0)))
  let e3  : Prop := (t23 (M := M) (fun x0_0 : M => (a0)))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p405 (M := M) (e0 z0)
  have v1 : ((show Prop from (t8 (M := M) (fun x0_0 : M => (e1 x0_0))))) := b325 (M := M) (fun w0 : M => (e1 w0)) ((fun w0 : M => v0 w0))
  have v2 : (e3) := (show (e3) from v1)
  exact v2
-- Actual MMB 674 nfnv
theorem p674 (a0 : M)  : (g786 (M := M) a0 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a0))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0)))
  let e3  : Prop := (t24 (M := M) (fun x0_0 : M => (a0)))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p405 (M := M) (e0 z0)
  have v1 : ((show Prop from (t8 (M := M) (fun x0_0 : M => (e1 x0_0))))) := b325 (M := M) (fun w0 : M => (e1 w0)) ((fun w0 : M => v0 w0))
  have v2 : (e3) := (show (e3) from v1)
  exact v2
-- Actual MMB 675 nfsri
theorem p675 (a2 : M → (M → Prop)) (h0 : (∀ z0 : M, (g787 (M := M) a2 z0))) : (g788 (M := M) a2 ) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u1 (a2 u0))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 x0_0 u0)))
  let e3  : Prop := (t23 (M := M) (fun x0_0 : M => (a2 x0_0)))
  have v0 : ((show Prop from (t8 (M := M) (fun x0_0 : M => (e1 x0_0))))) := b325 (M := M) (fun w0 : M => (e1 w0)) ((fun w0 : M => h0 w0))
  have v1 : (e3) := (show (e3) from v0)
  exact v1
-- Actual MMB 676 nfnri
theorem p676 (a2 : M → M) (h0 : (∀ z0 : M, (g789 (M := M) a2 z0))) : (g790 (M := M) a2 ) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 (a2 u0))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 x0_0 u0)))
  let e3  : Prop := (t24 (M := M) (fun x0_0 : M => (a2 x0_0)))
  have v0 : ((show Prop from (t8 (M := M) (fun x0_0 : M => (e1 x0_0))))) := b325 (M := M) (fun w0 : M => (e1 w0)) ((fun w0 : M => h0 w0))
  have v1 : (e3) := (show (e3) from v0)
  exact v1
-- Actual MMB 677 nfel2
theorem p677 (a1 : M) (a2 : M → (M → Prop)) (h0 : (g791 (M := M) a1 a2 )) : (g792 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a2 u1))
  let e2 (u0 : M) : Prop := (t16 (M := M) (a1) (a2 u0))
  let e3 (u0 : M) (u1 : M) : Prop := (t3 (e1 u0 u1) (e2 u1))
  let e4 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0) (e3 u0 u1))
  let e5 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e1 u0 x0_0)))
  let e6  : Prop := (t11 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e7 (u0 : M) : Prop := (t3 (e5 u0) (e6))
  let e8 (u0 : M) : Prop := (t0 (e0 u0) (e7 u0))
  let e9  : Prop := (t8 (M := M) (fun x0_0 : M => (e5 x0_0)))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e4 z0 z1))) := fun z0 : M => fun z1 : M => p572 (M := M) (a2 z1) z0 (a1)
  have v1 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p404 (M := M) (e0 z0) (fun w1 : M => (e1 z0 w1)) (fun w1 : M => (e2 w1)) ((fun w1 : M => v0 z0 w1))
  have v2 : ((show Prop from (t0 (e9) (e6)))) := p440 (M := M) (a1) (fun w0 : M => (e5 w0)) (e6) ((fun w0 : M => v1 w0))
  have v3 : (e9) := (show (e9) from h0)
  have v4 : (e6) := b3 (e9) (e6) (v2) (v3)
  exact v4
-- Actual MMB 678 nfsx
theorem p679 (a1 : M → M) (a2 : M → M) (h0 : (g796 (M := M) a1 a2 )) (h1 : (g797 (M := M) a1 a2 )) : (g798 (M := M) a1 a2 ) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a1 u1))
  let e1 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a2 u1))
  let e2 (u0 : M) (u1 : M) : Prop := (t2 (e0 u0 u1) (e1 u0 u1))
  let e3 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (e2 x0_0 u0)))
  let e4 (u0 : M) : Prop := (t10 (M := M) (a1 u0) (a2 u0))
  let e5 (u0 : M) : Prop := (t3 (e3 u0) (e4 u0))
  let e6 (u0 : M) : Prop := (t3 (e4 u0) (e3 u0))
  let e7 (u0 : M) : Prop := (t0 (e5 u0) (e6 u0))
  let e8 (u0 : M) (u1 : M) : Prop := (t3 (e1 u0 u1) (e4 u1))
  let e9 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e8 u0 u1))
  let e10 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0 x0_0)))
  let e11  : Prop := (t8 (M := M) (fun x0_0 : M => (e10 x0_0)))
  let e12 (u0 : M) : Prop := (t0 (e11) (e10 u0))
  let e13 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e1 u0 x0_0)))
  let e14  : Prop := (t8 (M := M) (fun x0_0 : M => (e13 x0_0)))
  let e15 (u0 : M) : Prop := (t0 (e14) (e13 u0))
  let e16 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0 x0_0)))
  have v0 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p142 (e3 z0) (e4 z0)
  have v1 : (∀ z0 : M, (∀ z1 : M, (e9 z0 z1))) := fun z0 : M => fun z1 : M => p346 (M := M) z0 (a1 z1) (a2 z1)
  have v2 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p543 (M := M) (a1 z0) (fun w0 : M => (e1 w0 z0)) (e4 z0) ((fun w0 : M => v1 w0 z0))
  have v3 : (∀ z0 : M, (e6 z0)) := fun z0 : M => b3 (e5 z0) (e6 z0) (v0 z0) (v2 z0)
  have v4 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p392 (M := M) (fun w0 : M => (e10 w0)) z0
  have v5 : (e11) := (show (e11) from h0)
  have v6 : (∀ z0 : M, (e10 z0)) := fun z0 : M => b3 (e11) (e10 z0) (v4 z0) (v5)
  have v7 : (∀ z0 : M, (e15 z0)) := fun z0 : M => p392 (M := M) (fun w0 : M => (e13 w0)) z0
  have v8 : (e14) := (show (e14) from h1)
  have v9 : (∀ z0 : M, (e13 z0)) := fun z0 : M => b3 (e14) (e13 z0) (v7 z0) (v8)
  have v10 : (∀ z0 : M, (e16 z0)) := fun z0 : M => p413 (M := M) (fun w0 : M => (e0 z0 w0)) (fun w0 : M => (e1 z0 w0)) (v6 z0) (v9 z0)
  have v11 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e3 x0_0))))) := p417 (M := M) (fun w0 : M => (fun w1 : M => (e2 w1 w0))) ((fun w1 : M => v10 w1))
  have v12 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e4 x0_0))))) := p409 (M := M) (fun w0 : M => (e4 w0)) (fun w0 : M => (e3 w0)) ((fun w0 : M => v3 w0)) (v11)
  exact v12
-- Actual MMB 680 nfeq2
theorem p680 (a0 : M) (a2 : M → M) (h0 : (g799 (M := M) a0 a2 )) : (g800 (M := M) a0 a2 ) := by
  let e1 (u0 : M) : Prop := (t10 (M := M) (a0) (a2 u0))
  have v0 : ((show Prop from (t24 (M := M) (fun x0_0 : M => (a0))))) := p674 (M := M) (a0)
  have v1 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e1 x0_0))))) := p679 (M := M) (fun w0 : M => (a0)) (fun w0 : M => (a2 w0)) (v0) (h0)
  exact v1
-- Actual MMB 681 nfsb1h
theorem p681 (a1 : M → M) (a2 : M → Prop) (h0 : (g801 (M := M) a1 a2 )) : (g802 (M := M) a1 a2 ) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a1 u1))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0 x0_0)))
  let e2 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e3 (u0 : M) (u1 : M) : Prop := (t0 (e2 u0 u1) (a2 u1))
  let e4 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e3 u0 x0_0)))
  let e5 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e4 u0)))
  let e6 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e4 u0))
  let e7 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e6 u0 x0_0)))
  let e8 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e6 x0_0 u0)))
  let e10 (u0 : M) : Prop := (t14 (M := M) (a1 u0) (fun x0_1 : M => (a2 x0_1)))
  let e11  : Prop := (t11 (M := M) (fun x0_0 : M => (e10 x0_0)))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p680 (M := M) z0 (fun w1 : M => (a1 w1)) (h0)
  have v1 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p418 (M := M) (fun w0 : M => (e3 z0 w0))
  have v2 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p412 (M := M) (fun w0 : M => (e0 z0 w0)) (fun w0 : M => (e4 z0)) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e8 x0_0))))) := p410 (M := M) (fun w0 : M => (fun w1 : M => (e6 w1 w0))) ((fun w1 : M => v2 w1))
  have v4 : (e11) := (show (e11) from v3)
  exact v4
-- Actual MMB 682 nfsbh
theorem p682 (a2 : M → M → M) (a3 : M → M → Prop) (h0 : (∀ z0 : M, (g803 (M := M) a2 a3 z0))) (h1 : (∀ z0 : M, (g804 (M := M) a2 a3 z0))) : (∀ z0 : M, (g805 (M := M) a2 a3 z0)) := by
  let e0 (u0 : M) (u1 : M) (u2 : M) : Prop := (t10 (M := M) u0 (a2 u1 u2))
  let e1 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0 x0_0 u1)))
  let e2 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e3 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0 u1)))
  let e4 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e2 u0 u2) (a3 u1 u2))
  let e5 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e4 u0 x0_0 u1)))
  let e6 (u0 : M) (u1 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e4 u0 u1 x0_0)))
  let e7 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e6 u0 x0_0)))
  let e8 (u0 : M) (u1 : M) (u2 : M) : Prop := (t0 (e0 u0 u1 u2) (e6 u0 u1))
  let e9 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e8 u0 x0_0 u1)))
  let e10 (u0 : M) (u1 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e8 x0_0 u0 u1)))
  let e11 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e10 x0_0 u0)))
  let e12 (u0 : M) (u1 : M) : Prop := (t14 (M := M) (a2 u0 u1) (fun x0_1 : M => (a3 u0 x0_1)))
  let e13 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e12 x0_0 u0)))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e1 z0 z1))) := fun z0 : M => fun z1 : M => p680 (M := M) z0 (fun w1 : M => (a2 w1 z1)) (h0 z1)
  have v1 : (∀ z0 : M, (∀ z1 : M, (e3 z0 z1))) := fun z0 : M => fun z1 : M => p405 (M := M) (e2 z0 z1)
  have v2 : (∀ z0 : M, (∀ z1 : M, (e5 z0 z1))) := fun z0 : M => fun z1 : M => p412 (M := M) (fun w0 : M => (e2 z0 z1)) (fun w0 : M => (a3 w0 z1)) (v1 z0 z1) (h1 z1)
  have v3 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p410 (M := M) (fun w0 : M => (fun w1 : M => (e4 z0 w0 w1))) ((fun w1 : M => v2 z0 w1))
  have v4 : (∀ z0 : M, (∀ z1 : M, (e9 z0 z1))) := fun z0 : M => fun z1 : M => p412 (M := M) (fun w0 : M => (e0 z0 w0 z1)) (fun w0 : M => (e6 z0 w0)) (v0 z0 z1) (v3 z0)
  have v5 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p410 (M := M) (fun w0 : M => (fun w1 : M => (e8 w1 w0 z0))) ((fun w1 : M => v4 w1 z0))
  have v6 : (∀ z0 : M, (e13 z0)) := (show (∀ z0 : M, (e13 z0)) from v5)
  exact v6
-- Actual MMB 683 nfel
theorem p683 (a1 : M → M) (a2 : M → (M → Prop)) (h0 : (g806 (M := M) a1 a2 )) (h1 : (g807 (M := M) a1 a2 )) : (g808 (M := M) a1 a2 ) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a1 u1))
  let e1 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a2 u1))
  let e2 (u0 : M) (u1 : M) : Prop := (t2 (e0 u0 u1) (e1 u0 u1))
  let e3 (u0 : M) : Prop := (t9 (M := M) (fun x0_0 : M => (e2 x0_0 u0)))
  let e4 (u0 : M) : Prop := (t16 (M := M) (a1 u0) (a2 u0))
  let e5 (u0 : M) : Prop := (t3 (e3 u0) (e4 u0))
  let e6 (u0 : M) : Prop := (t3 (e4 u0) (e3 u0))
  let e7 (u0 : M) : Prop := (t0 (e5 u0) (e6 u0))
  let e8 (u0 : M) (u1 : M) : Prop := (t3 (e1 u0 u1) (e4 u1))
  let e9 (u0 : M) (u1 : M) : Prop := (t0 (e0 u0 u1) (e8 u0 u1))
  let e10 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0 x0_0)))
  let e11  : Prop := (t8 (M := M) (fun x0_0 : M => (e10 x0_0)))
  let e12 (u0 : M) : Prop := (t0 (e11) (e10 u0))
  let e13 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e1 u0 x0_0)))
  let e14  : Prop := (t8 (M := M) (fun x0_0 : M => (e13 x0_0)))
  let e15 (u0 : M) : Prop := (t0 (e14) (e13 u0))
  let e16 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0 x0_0)))
  have v0 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p142 (e3 z0) (e4 z0)
  have v1 : (∀ z0 : M, (∀ z1 : M, (e9 z0 z1))) := fun z0 : M => fun z1 : M => p572 (M := M) (a2 z1) z0 (a1 z1)
  have v2 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p543 (M := M) (a1 z0) (fun w0 : M => (e1 w0 z0)) (e4 z0) ((fun w0 : M => v1 w0 z0))
  have v3 : (∀ z0 : M, (e6 z0)) := fun z0 : M => b3 (e5 z0) (e6 z0) (v0 z0) (v2 z0)
  have v4 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p392 (M := M) (fun w0 : M => (e10 w0)) z0
  have v5 : (e11) := (show (e11) from h0)
  have v6 : (∀ z0 : M, (e10 z0)) := fun z0 : M => b3 (e11) (e10 z0) (v4 z0) (v5)
  have v7 : (∀ z0 : M, (e15 z0)) := fun z0 : M => p392 (M := M) (fun w0 : M => (e13 w0)) z0
  have v8 : (e14) := (show (e14) from h1)
  have v9 : (∀ z0 : M, (e13 z0)) := fun z0 : M => b3 (e14) (e13 z0) (v7 z0) (v8)
  have v10 : (∀ z0 : M, (e16 z0)) := fun z0 : M => p413 (M := M) (fun w0 : M => (e0 z0 w0)) (fun w0 : M => (e1 z0 w0)) (v6 z0) (v9 z0)
  have v11 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e3 x0_0))))) := p417 (M := M) (fun w0 : M => (fun w1 : M => (e2 w1 w0))) ((fun w1 : M => v10 w1))
  have v12 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e4 x0_0))))) := p409 (M := M) (fun w0 : M => (e4 w0)) (fun w0 : M => (e3 w0)) ((fun w0 : M => v3 w0)) (v11)
  exact v12
-- Actual MMB 684 nfab1
theorem p684 (a1 : M → Prop)  : (g809 (M := M) a1 ) := by
  let e0  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (e0))
  let e2 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a1 x0_1)))
  let e3 (u0 : M) : Prop := (t3 (e1 u0) (e2 u0))
  let e4 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0)))
  let e5 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e1 u0)))
  have v0 : (∀ z0 : M, (e3 z0)) := fun z0 : M => b552 (M := M) z0 (fun w1 : M => (a1 w1))
  have v1 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p518 (M := M) z0 (fun w0 : M => (a1 w0))
  have v2 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p409 (M := M) (fun w0 : M => (e1 z0)) (fun w0 : M => (e2 z0)) ((fun w0 : M => v0 z0)) (v1 z0)
  have v3 : ((show Prop from (t23 (M := M) (fun x0_0 : M => (e0))))) := p675 (M := M) (fun w0 : M => (e0)) ((fun w1 : M => v2 w1))
  exact v3
-- Actual MMB 685 nfab
theorem p685 (a2 : M → M → Prop) (h0 : (∀ z0 : M, (g431 (M := M) a2 z0))) : (g810 (M := M) a2 ) := by
  let e0 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a2 u0 x0_0)))
  let e1 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (e0 u1))
  let e2 (u0 : M) (u1 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a2 u1 x0_1)))
  let e3 (u0 : M) (u1 : M) : Prop := (t3 (e1 u0 u1) (e2 u0 u1))
  let e4 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0 x0_0)))
  let e5 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e1 u0 x0_0)))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e3 z0 z1))) := fun z0 : M => fun z1 : M => b552 (M := M) z0 (fun w1 : M => (a2 z1 w1))
  have v1 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p519 (M := M) (fun w1 : M => z0) (fun w0 : M => (fun w1 : M => (a2 w0 w1))) ((fun w1 : M => h0 w1)) 0
  have v2 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p409 (M := M) (fun w0 : M => (e1 z0 w0)) (fun w0 : M => (e2 z0 w0)) ((fun w0 : M => v0 z0 w0)) (v1 z0)
  have v3 : ((show Prop from (t23 (M := M) (fun x0_0 : M => (e0 x0_0))))) := p675 (M := M) (fun w0 : M => (e0 w0)) ((fun w1 : M => v2 w1))
  exact v3
-- Actual MMB 686 nfeqs
theorem p686 (a1 : M → (M → Prop)) (a2 : M → (M → Prop)) (h0 : (g795 (M := M) a1 a2 )) (h1 : (g794 (M := M) a1 a2 )) : (g811 (M := M) a1 a2 ) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a1 u1))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0 x0_0)))
  let e2 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a2 u1))
  let e3 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0 x0_0)))
  let e4 (u0 : M) (u1 : M) : Prop := (t3 (e0 u0 u1) (e2 u0 u1))
  let e5 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e4 u0 x0_0)))
  let e6 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e4 x0_0 u0)))
  let e8 (u0 : M) : Prop := (t17 (M := M) (a1 u0) (a2 u0))
  let e9  : Prop := (t11 (M := M) (fun x0_0 : M => (e8 x0_0)))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p677 (M := M) z0 (fun w0 : M => (a1 w0)) (h0)
  have v1 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p677 (M := M) z0 (fun w0 : M => (a2 w0)) (h1)
  have v2 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p415 (M := M) (fun w0 : M => (e0 z0 w0)) (fun w0 : M => (e2 z0 w0)) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t11 (M := M) (fun x0_0 : M => (e6 x0_0))))) := p410 (M := M) (fun w0 : M => (fun w1 : M => (e4 w1 w0))) ((fun w1 : M => v2 w1))
  have v4 : (e9) := (show (e9) from v3)
  exact v4
-- Actual MMB 687 nfnx
theorem p687 (a1 : M → M) (a2 : M → M) (h0 : (∀ z0 : M, (g812 (M := M) a1 a2 z0))) (h1 : (g797 (M := M) a1 a2 )) : (g796 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) (a1 u0) (a2 u0))
  let e1 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a1 u1))
  let e2 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (a2 u1))
  let e3 (u0 : M) (u1 : M) : Prop := (t3 (e1 u0 u1) (e2 u0 u1))
  let e4 (u0 : M) (u1 : M) : Prop := (t0 (e0 u1) (e3 u0 u1))
  let e5 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0 x0_0)))
  let e6 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e1 u0 x0_0)))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e4 z0 z1))) := fun z0 : M => fun z1 : M => p347 (M := M) z0 (a1 z1) (a2 z1)
  have v1 : (∀ z0 : M, (∀ z1 : M, (e3 z0 z1))) := fun z0 : M => fun z1 : M => b3 (e0 z1) (e3 z0 z1) (v0 z0 z1) (h0 z1)
  have v2 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p680 (M := M) z0 (fun w1 : M => (a2 w1)) (h1)
  have v3 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p409 (M := M) (fun w0 : M => (e1 z0 w0)) (fun w0 : M => (e2 z0 w0)) ((fun w0 : M => v1 z0 w0)) (v2 z0)
  have v4 : ((show Prop from (t24 (M := M) (fun x0_0 : M => (a1 x0_0))))) := p676 (M := M) (fun w0 : M => (a1 w0)) ((fun w1 : M => v3 w1))
  exact v4
-- Actual MMB 688 nfin
theorem p688 (a1 : M → (M → Prop)) (a2 : M → (M → Prop)) (h0 : (g795 (M := M) a1 a2 )) (h1 : (g794 (M := M) a1 a2 )) : (g813 (M := M) a1 a2 ) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a1 u1))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0 x0_0)))
  let e2 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a2 u1))
  let e3 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0 x0_0)))
  let e4 (u0 : M) (u1 : M) : Prop := (t2 (e0 u0 u1) (e2 u0 u1))
  let e5 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e4 u0 x0_0)))
  let e6 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e4 x0_0 u0)))
  let e8 (u0 : M) : (M → Prop) := (t19 (M := M) (a1 u0) (a2 u0))
  let e9  : Prop := (t23 (M := M) (fun x0_0 : M => (e8 x0_0)))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p677 (M := M) z0 (fun w0 : M => (a1 w0)) (h0)
  have v1 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p677 (M := M) z0 (fun w0 : M => (a2 w0)) (h1)
  have v2 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p413 (M := M) (fun w0 : M => (e0 z0 w0)) (fun w0 : M => (e2 z0 w0)) (v0 z0) (v1 z0)
  have v3 : ((show Prop from (t23 (M := M) (fun x0_0 : M => (e6 x0_0))))) := p685 (M := M) (fun w0 : M => (fun w1 : M => (e4 w1 w0))) ((fun w1 : M => v2 w1))
  have v4 : (e9) := (show (e9) from v3)
  exact v4
-- Actual MMB 689 nfss
theorem p691 (a0 : (M → Prop)) (a1 : Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (g816 (M := M) a0 a1 a3 z0))) : (g817 (M := M) a0 a1 a3 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e1 (u0 : M) : Prop := (t3 (e0 u0) (a3 u0))
  let e2 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e1 u0)))
  let e3 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e4 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e3 u0)))
  let e5  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a3 x0_0)))
  let e7 (u0 : M) : Prop := (t16 (M := M) u0 (e5))
  let e8 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e7 u0)))
  let e9 (u0 : M) : Prop := (t3 (e3 u0) (e7 u0))
  let e10 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e9 u0)))
  let e11 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e12 (u0 : M) (u1 : M) : Prop := (t3 (e0 u1) (e3 u0))
  let e13 (u0 : M) (u1 : M) : Prop := (t0 (e11 u0 u1) (e12 u0 u1))
  let e14 (u0 : M) : Prop := (t16 (M := M) u0 (e5))
  let e15 (u0 : M) : Prop := (t3 (e14 u0) (a3 u0))
  let e16 (u0 : M) (u1 : M) : Prop := (t3 (e14 u1) (e7 u0))
  let e17 (u0 : M) (u1 : M) : Prop := (t0 (e11 u0 u1) (e16 u0 u1))
  let e18 (u0 : M) (u1 : M) : Prop := (t3 (a3 u1) (e7 u0))
  let e19 (u0 : M) (u1 : M) : Prop := (t0 (e11 u0 u1) (e18 u0 u1))
  let e20 (u0 : M) (u1 : M) : Prop := (t3 (e1 u1) (e9 u0))
  let e21 (u0 : M) (u1 : M) : Prop := (t0 (e11 u0 u1) (e20 u0 u1))
  let e22  : Prop := (t8 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e25  : Prop := (t17 (M := M) (a0) (e5))
  let e26  : Prop := (t3 (e22) (e25))
  have v0 : (∀ z0 : M, (e2 z0)) := fun z0 : M => p405 (M := M) (e1 z0)
  have v1 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p405 (M := M) (e3 z0)
  have v2 : ((show Prop from (t23 (M := M) (fun x0_0 : M => (e5))))) := p684 (M := M) (fun w0 : M => (a3 w0))
  have v3 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p677 (M := M) z0 (fun w0 : M => (e5)) (v2)
  have v4 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p415 (M := M) (fun w0 : M => (e3 z0)) (fun w0 : M => (e7 z0)) (v1 z0) (v3 z0)
  have v5 : (∀ z0 : M, (∀ z1 : M, (e13 z0 z1))) := fun z0 : M => fun z1 : M => p572 (M := M) (a0) z1 z0
  have v6 : (∀ z0 : M, (e15 z0)) := fun z0 : M => p598 (M := M) (fun w0 : M => (a3 w0)) z0
  have v7 : (∀ z0 : M, (∀ z1 : M, (e17 z0 z1))) := fun z0 : M => fun z1 : M => p572 (M := M) (e5) z1 z0
  have v8 : (∀ z0 : M, (∀ z1 : M, (e19 z0 z1))) := fun z0 : M => fun z1 : M => p158 (e11 z0 z1) (a3 z1) (e14 z1) (e7 z0) (v6 z1) (v7 z0 z1)
  have v9 : (∀ z0 : M, (∀ z1 : M, (e21 z0 z1))) := fun z0 : M => fun z1 : M => p233 (e11 z0 z1) (e0 z1) (e3 z0) (a3 z1) (e7 z0) (v5 z0 z1) (v8 z0 z1)
  have v10 : ((show Prop from (t3 (e22) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e9 x0_0)))))))) := p480 (M := M) (fun w0 : M => (fun w1 : M => (e1 w0))) (fun w0 : M => (fun w1 : M => (e9 w1))) ((fun w0 : M => v0 w0)) ((fun w1 : M => v4 w1)) ((fun w0 : M => (fun w1 : M => v9 w1 w0))) 0 0
  have v11 : (e26) := (show (e26) from v10)
  have v12 : ((show Prop from (t0 (a1) (e22)))) := p338 (M := M) (a1) (fun w0 : M => (e1 w0)) ((fun w0 : M => h0 w0))
  have v13 : ((show Prop from (t0 (a1) (e25)))) := p153 (a1) (e22) (e25) (v11) (v12)
  exact v13
-- Actual MMB 692 eqab2i
theorem p692 (a0 : (M → Prop)) (a2 : M → Prop) (h0 : (∀ z0 : M, (g818 (M := M) a0 a2 z0))) : (g819 (M := M) a0 a2 ) := by
  let e0  : Prop := (t6)
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e2 (u0 : M) : Prop := (t3 (e1 u0) (a2 u0))
  let e3 (u0 : M) : Prop := (t0 (e0) (e2 u0))
  let e5  : Prop := (t17 (M := M) (a0) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (a2 x0_0))))))
  have v0 : (∀ z0 : M, (e3 z0)) := fun z0 : M => p4 (e0) (e2 z0) (h0 z0)
  have v1 : ((show Prop from (t0 (e0) (e5)))) := p691 (M := M) (a0) (e0) (fun w2 : M => (a2 w2)) ((fun w2 : M => v0 w2))
  have v2 : (e5) := p318 (e5) (v1)
  exact v2
-- Actual MMB 693 eqab1d
theorem p693 (a0 : (M → Prop)) (a1 : Prop) (a3 : M → Prop) (h0 : (∀ z0 : M, (g820 (M := M) a0 a1 a3 z0))) : (g821 (M := M) a0 a1 a3 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e1 (u0 : M) : Prop := (t3 (e0 u0) (a3 u0))
  let e2 (u0 : M) : Prop := (t0 (a1) (e1 u0))
  let e3  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a3 x0_0)))
  have v0 : (∀ z0 : M, (e2 z0)) := fun z0 : M => p144 (a1) (a3 z0) (e0 z0) (h0 z0)
  have v1 : ((show Prop from (t0 (a1) ((show Prop from (t17 (M := M) (a0) (e3))))))) := p691 (M := M) (a0) (a1) (fun w2 : M => (a3 w2)) ((fun w2 : M => v0 w2))
  have v2 : ((show Prop from (t0 (a1) ((show Prop from (t17 (M := M) (e3) (a0))))))) := p563 (M := M) (a0) (e3) (a1) (v1)
  exact v2
-- Actual MMB 694 eqab1i
theorem p695 (a1 : M → Prop) (a2 : M → Prop)  : (g824 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : Prop := (t0 (a1 u0) (a2 u0))
  let e1 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e0 u0)))
  let e2  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a1 x0_0)))
  let e4 (u0 : M) : Prop := (t16 (M := M) u0 (e2))
  let e5 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e4 u0)))
  let e6  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a2 x0_0)))
  let e8 (u0 : M) : Prop := (t16 (M := M) u0 (e6))
  let e9 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e8 u0)))
  let e10 (u0 : M) : Prop := (t0 (e4 u0) (e8 u0))
  let e11 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e10 u0)))
  let e12 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a1 x0_1)))
  let e13 (u0 : M) : Prop := (t3 (e4 u0) (e12 u0))
  let e14 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e15 (u0 : M) (u1 : M) : Prop := (t3 (a1 u1) (e12 u0))
  let e16 (u0 : M) (u1 : M) : Prop := (t0 (e14 u0 u1) (e15 u0 u1))
  let e17 (u0 : M) (u1 : M) : Prop := (t3 (a1 u1) (e4 u0))
  let e18 (u0 : M) (u1 : M) : Prop := (t0 (e14 u0 u1) (e17 u0 u1))
  let e19 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a2 x0_1)))
  let e20 (u0 : M) : Prop := (t3 (e8 u0) (e19 u0))
  let e21 (u0 : M) (u1 : M) : Prop := (t3 (a2 u1) (e19 u0))
  let e22 (u0 : M) (u1 : M) : Prop := (t0 (e14 u0 u1) (e21 u0 u1))
  let e23 (u0 : M) (u1 : M) : Prop := (t3 (a2 u1) (e8 u0))
  let e24 (u0 : M) (u1 : M) : Prop := (t0 (e14 u0 u1) (e23 u0 u1))
  let e25 (u0 : M) (u1 : M) : Prop := (t3 (e0 u1) (e10 u0))
  let e26 (u0 : M) (u1 : M) : Prop := (t0 (e14 u0 u1) (e25 u0 u1))
  let e27  : Prop := (t8 (M := M) (fun x0_0 : M => (e0 x0_0)))
  let e31  : Prop := (t3 (e27) ((show Prop from (t18 (M := M) (e2) (e6)))))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p405 (M := M) (e0 z0)
  have v1 : ((show Prop from (t23 (M := M) (fun x0_0 : M => (e2))))) := p684 (M := M) (fun w0 : M => (a1 w0))
  have v2 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p677 (M := M) z0 (fun w0 : M => (e2)) (v1)
  have v3 : ((show Prop from (t23 (M := M) (fun x0_0 : M => (e6))))) := p684 (M := M) (fun w0 : M => (a2 w0))
  have v4 : (∀ z0 : M, (e9 z0)) := fun z0 : M => p677 (M := M) z0 (fun w0 : M => (e6)) (v3)
  have v5 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p412 (M := M) (fun w0 : M => (e4 z0)) (fun w0 : M => (e8 z0)) (v2 z0) (v4 z0)
  have v6 : (∀ z0 : M, (e13 z0)) := fun z0 : M => b552 (M := M) z0 (fun w1 : M => (a1 w1))
  have v7 : (∀ z0 : M, (∀ z1 : M, (e16 z0 z1))) := fun z0 : M => fun z1 : M => p516 (M := M) z0 (fun w0 : M => (a1 w0)) z1
  have v8 : (∀ z0 : M, (∀ z1 : M, (e18 z0 z1))) := fun z0 : M => fun z1 : M => p160 (e14 z0 z1) (a1 z1) (e12 z0) (e4 z0) (v6 z0) (v7 z0 z1)
  have v9 : (∀ z0 : M, (e20 z0)) := fun z0 : M => b552 (M := M) z0 (fun w1 : M => (a2 w1))
  have v10 : (∀ z0 : M, (∀ z1 : M, (e22 z0 z1))) := fun z0 : M => fun z1 : M => p516 (M := M) z0 (fun w0 : M => (a2 w0)) z1
  have v11 : (∀ z0 : M, (∀ z1 : M, (e24 z0 z1))) := fun z0 : M => fun z1 : M => p160 (e14 z0 z1) (a2 z1) (e19 z0) (e8 z0) (v9 z0) (v10 z0 z1)
  have v12 : (∀ z0 : M, (∀ z1 : M, (e26 z0 z1))) := fun z0 : M => fun z1 : M => p188 (e14 z0 z1) (a1 z1) (e4 z0) (a2 z1) (e8 z0) (v8 z0 z1) (v11 z0 z1)
  have v13 : ((show Prop from (t3 (e27) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e10 x0_0)))))))) := p480 (M := M) (fun w0 : M => (fun w1 : M => (e0 w0))) (fun w0 : M => (fun w1 : M => (e10 w1))) ((fun w0 : M => v0 w0)) ((fun w1 : M => v5 w1)) ((fun w0 : M => (fun w1 : M => v12 w1 w0))) 0 0
  have v14 : (e31) := (show (e31) from v13)
  exact v14
-- Actual MMB 696 ssabi
theorem p699 (a0 : (M → Prop)) (a2 : M → Prop)  : (g829 (M := M) a0 a2 ) := by
  let e0 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e1 (u0 : M) : Prop := (t0 (e0 u0) (a2 u0))
  let e2 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e1 u0)))
  let e3 (u0 : M) : Prop := (t16 (M := M) u0 (a0))
  let e4 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e3 u0)))
  let e5  : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (a2 x0_0)))
  let e7 (u0 : M) : Prop := (t16 (M := M) u0 (e5))
  let e8 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e7 u0)))
  let e9 (u0 : M) : Prop := (t0 (e3 u0) (e7 u0))
  let e10 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e9 u0)))
  let e11 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u1 u0)
  let e12 (u0 : M) (u1 : M) : Prop := (t3 (e0 u1) (e3 u0))
  let e13 (u0 : M) (u1 : M) : Prop := (t0 (e11 u0 u1) (e12 u0 u1))
  let e14 (u0 : M) : Prop := (t14 (M := M) u0 (fun x0_1 : M => (a2 x0_1)))
  let e15 (u0 : M) : Prop := (t3 (e7 u0) (e14 u0))
  let e16 (u0 : M) (u1 : M) : Prop := (t3 (a2 u1) (e14 u0))
  let e17 (u0 : M) (u1 : M) : Prop := (t0 (e11 u0 u1) (e16 u0 u1))
  let e18 (u0 : M) (u1 : M) : Prop := (t3 (a2 u1) (e7 u0))
  let e19 (u0 : M) (u1 : M) : Prop := (t0 (e11 u0 u1) (e18 u0 u1))
  let e20 (u0 : M) (u1 : M) : Prop := (t3 (e1 u1) (e9 u0))
  let e21 (u0 : M) (u1 : M) : Prop := (t0 (e11 u0 u1) (e20 u0 u1))
  let e22  : Prop := (t8 (M := M) (fun x0_0 : M => (e1 x0_0)))
  let e26  : Prop := (t3 (e22) ((show Prop from (t18 (M := M) (a0) (e5)))))
  have v0 : (∀ z0 : M, (e2 z0)) := fun z0 : M => p405 (M := M) (e1 z0)
  have v1 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p405 (M := M) (e3 z0)
  have v2 : ((show Prop from (t23 (M := M) (fun x0_0 : M => (e5))))) := p684 (M := M) (fun w0 : M => (a2 w0))
  have v3 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p677 (M := M) z0 (fun w0 : M => (e5)) (v2)
  have v4 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p412 (M := M) (fun w0 : M => (e3 z0)) (fun w0 : M => (e7 z0)) (v1 z0) (v3 z0)
  have v5 : (∀ z0 : M, (∀ z1 : M, (e13 z0 z1))) := fun z0 : M => fun z1 : M => p572 (M := M) (a0) z1 z0
  have v6 : (∀ z0 : M, (e15 z0)) := fun z0 : M => b552 (M := M) z0 (fun w1 : M => (a2 w1))
  have v7 : (∀ z0 : M, (∀ z1 : M, (e17 z0 z1))) := fun z0 : M => fun z1 : M => p516 (M := M) z0 (fun w0 : M => (a2 w0)) z1
  have v8 : (∀ z0 : M, (∀ z1 : M, (e19 z0 z1))) := fun z0 : M => fun z1 : M => p160 (e11 z0 z1) (a2 z1) (e14 z0) (e7 z0) (v6 z0) (v7 z0 z1)
  have v9 : (∀ z0 : M, (∀ z1 : M, (e21 z0 z1))) := fun z0 : M => fun z1 : M => p188 (e11 z0 z1) (e0 z1) (e3 z0) (a2 z1) (e7 z0) (v5 z0 z1) (v8 z0 z1)
  have v10 : ((show Prop from (t3 (e22) ((show Prop from (t8 (M := M) (fun x0_0 : M => (e9 x0_0)))))))) := p480 (M := M) (fun w0 : M => (fun w1 : M => (e1 w0))) (fun w0 : M => (fun w1 : M => (e9 w1))) ((fun w0 : M => v0 w0)) ((fun w1 : M => v4 w1)) ((fun w0 : M => (fun w1 : M => v9 w1 w0))) 0 0
  have v11 : (e26) := (show (e26) from v10)
  exact v11
-- Actual MMB 700 elabed1
theorem p703 (a1 : M → M) (a2 : M) (a3 : M → (M → Prop))  : (∀ z0 : M, (g835 (M := M) a1 a2 a3 z0)) := by
  let e0 (u0 : M) : (M → Prop) := (t25 (M := M) (a1 u0) (fun x0_1 : M => (a3 x0_1)))
  let e1 (u0 : M) : Prop := (t16 (M := M) (a2) (e0 u0))
  let e2 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a3 u1))
  let e3 (u0 : M) (u1 : M) : Prop := (t14 (M := M) (a1 u1) (fun x0_1 : M => (e2 u0 x0_1)))
  let e4 (u0 : M) : Prop := (t14 (M := M) (a2) (fun x0_1 : M => (e3 x0_1 u0)))
  let e5 (u0 : M) : Prop := (t16 (M := M) (a2) (a3 u0))
  let e6 (u0 : M) : Prop := (t14 (M := M) (a1 u0) (fun x0_1 : M => (e5 x0_1)))
  let e7 (u0 : M) : Prop := (t3 (e1 u0) (e4 u0))
  let e8 (u0 : M) : Prop := (t3 (e4 u0) (e6 u0))
  let e9 (u0 : M) : Prop := (t3 (e1 u0) (e6 u0))
  let e10 (u0 : M) : Prop := (t0 (e8 u0) (e9 u0))
  let e11 (u0 : M) : Prop := (t0 (e7 u0) (e10 u0))
  let e12 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e3 x0_0 u0)))
  let e13 (u0 : M) : Prop := (t16 (M := M) (a2) (e12 u0))
  let e14 (u0 : M) : Prop := (t3 (e13 u0) (e4 u0))
  let e15 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e16 (u0 : M) (u1 : M) : Prop := (t3 (e2 u0 u1) (e5 u1))
  let e17 (u0 : M) (u1 : M) : Prop := (t0 (e15 u0) (e16 u0 u1))
  let e18 (u0 : M) (u1 : M) : Prop := (t3 (e3 u0 u1) (e6 u1))
  let e19 (u0 : M) (u1 : M) : Prop := (t0 (e15 u0) (e18 u0 u1))
  have v0 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p149 (e1 z0) (e4 z0) (e6 z0)
  have v1 : (∀ z0 : M, (e14 z0)) := fun z0 : M => b552 (M := M) (a2) (fun w1 : M => (e3 w1 z0))
  have v2 : (∀ z0 : M, (e7 z0)) := (show (∀ z0 : M, (e7 z0)) from v1)
  have v3 : (∀ z0 : M, (e10 z0)) := fun z0 : M => b3 (e7 z0) (e10 z0) (v0 z0) (v2 z0)
  have v4 : (∀ z0 : M, (∀ z1 : M, (e17 z0 z1))) := fun z0 : M => fun z1 : M => p572 (M := M) (a3 z1) z0 (a2)
  have v5 : (∀ z0 : M, (∀ z1 : M, (e19 z0 z1))) := fun z0 : M => fun z1 : M => p523 (M := M) (e15 z0) (fun w1 : M => (a1 w1)) (fun w1 : M => (e2 z0 w1)) (fun w1 : M => (e5 w1)) ((fun w1 : M => v4 z0 w1)) z1
  have v6 : (∀ z0 : M, (e8 z0)) := fun z0 : M => p528 (M := M) (a2) (fun w0 : M => (e3 w0 z0)) (e6 z0) ((fun w0 : M => v5 w0 z0))
  have v7 : (∀ z0 : M, (e9 z0)) := fun z0 : M => b3 (e8 z0) (e9 z0) (v3 z0) (v6 z0)
  exact v7
-- Actual MMB 704 sbsq
theorem p704 (a1 : M) (a2 : M → (M → Prop))  : (∀ z0 : M, (g836 (M := M) a1 a2 z0)) := by
  let e0  : (M → Prop) := (t25 (M := M) (a1) (fun x0_1 : M => (a2 x0_1)))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (e0))
  let e2 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a2 u1))
  let e3 (u0 : M) : Prop := (t14 (M := M) (a1) (fun x0_1 : M => (e2 u0 x0_1)))
  let e4 (u0 : M) : Prop := (t3 (e1 u0) (e3 u0))
  let e5 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e6 (u0 : M) (u1 : M) : Prop := (t3 (e2 u0 u1) (e3 u0))
  let e7 (u0 : M) (u1 : M) : Prop := (t0 (e5 u1) (e6 u0 u1))
  let e8 (u0 : M) (u1 : M) : Prop := (t3 (e2 u0 u1) (e1 u0))
  let e9 (u0 : M) (u1 : M) : Prop := (t0 (e5 u1) (e8 u0 u1))
  let e10 (u0 : M) : Prop := (t17 (M := M) (a2 u0) (e0))
  let e11 (u0 : M) : Prop := (t0 (e5 u0) (e10 u0))
  have v0 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p703 (M := M) (fun w0 : M => (a1)) z0 (fun w0 : M => (a2 w0)) 0
  have v1 : (∀ z0 : M, (∀ z1 : M, (e7 z0 z1))) := fun z0 : M => fun z1 : M => p516 (M := M) (a1) (fun w0 : M => (e2 z0 w0)) z1
  have v2 : (∀ z0 : M, (∀ z1 : M, (e9 z0 z1))) := fun z0 : M => fun z1 : M => p160 (e5 z1) (e2 z0 z1) (e3 z0) (e1 z0) (v0 z0) (v1 z0 z1)
  have v3 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p587 (M := M) (a2 z0) (e0) (e5 z0) ((fun w3 : M => v2 w3 z0))
  exact v3
-- Actual MMB 705 nfsbs1h
theorem p705 (a1 : M → M) (a2 : M → (M → Prop)) (h0 : (g806 (M := M) a1 a2 )) : (g837 (M := M) a1 a2 ) := by
  let e0 (u0 : M) : (M → Prop) := (t25 (M := M) (a1 u0) (fun x0_1 : M => (a2 x0_1)))
  let e1 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (e0 u1))
  let e2 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a2 u1))
  let e3 (u0 : M) (u1 : M) : Prop := (t14 (M := M) (a1 u1) (fun x0_1 : M => (e2 u0 x0_1)))
  let e4 (u0 : M) (u1 : M) : Prop := (t3 (e1 u0 u1) (e3 u0 u1))
  let e5 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e3 u0 x0_0)))
  let e6 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e1 u0 x0_0)))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e4 z0 z1))) := fun z0 : M => fun z1 : M => p703 (M := M) (fun w0 : M => (a1 w0)) z0 (fun w0 : M => (a2 w0)) z1
  have v1 : (∀ z0 : M, (e5 z0)) := fun z0 : M => p681 (M := M) (fun w0 : M => (a1 w0)) (fun w0 : M => (e2 z0 w0)) (h0)
  have v2 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p409 (M := M) (fun w0 : M => (e1 z0 w0)) (fun w0 : M => (e3 z0 w0)) ((fun w0 : M => v0 z0 w0)) (v1 z0)
  have v3 : ((show Prop from (t23 (M := M) (fun x0_0 : M => (e0 x0_0))))) := p675 (M := M) (fun w0 : M => (e0 w0)) ((fun w1 : M => v2 w1))
  exact v3
-- Actual MMB 706 nfsbs1
theorem p706 (a1 : M) (a2 : M → (M → Prop))  : (g838 (M := M) a1 a2 ) := by
  have v0 : ((show Prop from (t24 (M := M) (fun x0_0 : M => (a1))))) := p674 (M := M) (a1)
  have v1 : ((show Prop from (t23 (M := M) (fun x0_0 : M => ((show (M → Prop) from (t25 (M := M) (a1) (fun x0_1 : M => (a2 x0_1))))))))) := p705 (M := M) (fun w0 : M => (a1)) (fun w0 : M => (a2 w0)) (v0)
  exact v1
-- Actual MMB 707 nfsbsh
theorem p707 (a2 : M → M) (a3 : M → M → (M → Prop)) (h0 : (g839 (M := M) a2 a3 )) (h1 : (∀ z0 : M, (g840 (M := M) a2 a3 z0))) : (g841 (M := M) a2 a3 ) := by
  let e0 (u0 : M) : (M → Prop) := (t25 (M := M) (a2 u0) (fun x0_1 : M => (a3 u0 x0_1)))
  let e1 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (e0 u1))
  let e2 (u0 : M) (u1 : M) (u2 : M) : Prop := (t16 (M := M) u0 (a3 u1 u2))
  let e3 (u0 : M) (u1 : M) : Prop := (t14 (M := M) (a2 u1) (fun x0_1 : M => (e2 u0 u1 x0_1)))
  let e4 (u0 : M) (u1 : M) : Prop := (t3 (e1 u0 u1) (e3 u0 u1))
  let e5 (u0 : M) (u1 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e2 u0 x0_0 u1)))
  let e6 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e3 u0 x0_0)))
  let e7 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e1 u0 x0_0)))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e4 z0 z1))) := fun z0 : M => fun z1 : M => p703 (M := M) (fun w0 : M => (a2 z1)) z0 (fun w0 : M => (a3 z1 w0)) 0
  have v1 : (∀ z0 : M, (∀ z1 : M, (e5 z0 z1))) := fun z0 : M => fun z1 : M => p677 (M := M) z0 (fun w0 : M => (a3 w0 z1)) (h1 z1)
  have v2 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p682 (M := M) (fun w0 : M => (fun w1 : M => (a2 w0))) (fun w0 : M => (fun w1 : M => (e2 z0 w0 w1))) ((fun w1 : M => h0)) ((fun w1 : M => v1 z0 w1)) 0
  have v3 : (∀ z0 : M, (e7 z0)) := fun z0 : M => p409 (M := M) (fun w0 : M => (e1 z0 w0)) (fun w0 : M => (e3 z0 w0)) ((fun w0 : M => v0 z0 w0)) (v2 z0)
  have v4 : ((show Prop from (t23 (M := M) (fun x0_0 : M => (e0 x0_0))))) := p675 (M := M) (fun w0 : M => (e0 w0)) ((fun w1 : M => v3 w1))
  exact v4
-- Actual MMB 708 nfsbs
theorem p708 (a2 : M) (a3 : M → M → (M → Prop)) (h0 : (∀ z0 : M, (g842 (M := M) a2 a3 z0))) : (g843 (M := M) a2 a3 ) := by
  let e1 (u0 : M) : (M → Prop) := (t25 (M := M) (a2) (fun x0_1 : M => (a3 u0 x0_1)))
  have v0 : ((show Prop from (t24 (M := M) (fun x0_0 : M => (a2))))) := p674 (M := M) (a2)
  have v1 : ((show Prop from (t23 (M := M) (fun x0_0 : M => (e1 x0_0))))) := p707 (M := M) (fun w0 : M => (a2)) (fun w0 : M => (fun w1 : M => (a3 w0 w1))) (v0) ((fun w1 : M => h0 w1))
  exact v1
-- Actual MMB 709 sbseq1d
theorem p709 (a0 : Prop) (a2 : M) (a3 : M) (a4 : M → (M → Prop)) (h0 : (g844 (M := M) a0 a2 a3 a4 )) : (g845 (M := M) a0 a2 a3 a4 ) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a4 u1))
  let e1 (u0 : M) : Prop := (t14 (M := M) (a2) (fun x0_1 : M => (e0 u0 x0_1)))
  let e2 (u0 : M) : Prop := (t14 (M := M) (a3) (fun x0_1 : M => (e0 u0 x0_1)))
  let e3 (u0 : M) : Prop := (t3 (e1 u0) (e2 u0))
  let e4 (u0 : M) : Prop := (t0 (a0) (e3 u0))
  let e12  : Prop := (t0 (a0) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t25 (M := M) (a2) (fun x0_1 : M => (a4 x0_1))))) ((show (M → Prop) from (t25 (M := M) (a3) (fun x0_1 : M => (a4 x0_1)))))))))
  have v0 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p521 (M := M) (fun w0 : M => (a0)) (fun w0 : M => (a2)) (fun w0 : M => (a3)) (fun w0 : M => (e0 z0 w0)) ((fun w0 : M => h0)) 0
  have v1 : ((show Prop from (t0 (a0) ((show Prop from (t17 (M := M) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e1 x0_0))))) ((show (M → Prop) from (t15 (M := M) (fun x0_0 : M => (e2 x0_0))))))))))) := p584 (M := M) (a0) (fun w1 : M => (e1 w1)) (fun w1 : M => (e2 w1)) ((fun w1 : M => v0 w1))
  have v2 : (e12) := (show (e12) from v1)
  exact v2
-- Actual MMB 710 sbseq2d
theorem p710 (a0 : Prop) (a2 : M → M) (a3 : M → (M → Prop)) (a4 : M → (M → Prop)) (h0 : (∀ z0 : M, (g846 (M := M) a0 a2 a3 a4 z0))) : (∀ z0 : M, (g847 (M := M) a0 a2 a3 a4 z0)) := by
  let e0 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a3 u1))
  let e1 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a4 u1))
  let e2 (u0 : M) (u1 : M) : Prop := (t3 (e0 u0 u1) (e1 u0 u1))
  let e3 (u0 : M) (u1 : M) : Prop := (t0 (a0) (e2 u0 u1))
  let e4 (u0 : M) (u1 : M) : Prop := (t14 (M := M) (a2 u1) (fun x0_1 : M => (e0 u0 x0_1)))
  let e5 (u0 : M) (u1 : M) : Prop := (t14 (M := M) (a2 u1) (fun x0_1 : M => (e1 u0 x0_1)))
  let e6 (u0 : M) (u1 : M) : Prop := (t3 (e4 u0 u1) (e5 u0 u1))
  let e7 (u0 : M) (u1 : M) : Prop := (t0 (a0) (e6 u0 u1))
  let e8 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e4 x0_0 u0)))
  let e9 (u0 : M) : (M → Prop) := (t15 (M := M) (fun x0_0 : M => (e5 x0_0 u0)))
  let e10 (u0 : M) : Prop := (t17 (M := M) (e8 u0) (e9 u0))
  let e11 (u0 : M) : Prop := (t0 (a0) (e10 u0))
  let e12 (u0 : M) : (M → Prop) := (t25 (M := M) (a2 u0) (fun x0_1 : M => (a3 x0_1)))
  let e13 (u0 : M) : (M → Prop) := (t25 (M := M) (a2 u0) (fun x0_1 : M => (a4 x0_1)))
  let e14 (u0 : M) : Prop := (t17 (M := M) (e12 u0) (e13 u0))
  let e15 (u0 : M) : Prop := (t0 (a0) (e14 u0))
  have v0 : (∀ z0 : M, (∀ z1 : M, (e3 z0 z1))) := fun z0 : M => fun z1 : M => p575 (M := M) (a0) z0 (a3 z1) (a4 z1) (h0 z1)
  have v1 : (∀ z0 : M, (∀ z1 : M, (e7 z0 z1))) := fun z0 : M => fun z1 : M => p523 (M := M) (a0) (fun w1 : M => (a2 w1)) (fun w1 : M => (e0 z0 w1)) (fun w1 : M => (e1 z0 w1)) ((fun w1 : M => v0 z0 w1)) z1
  have v2 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p584 (M := M) (a0) (fun w1 : M => (e4 w1 z0)) (fun w1 : M => (e5 w1 z0)) ((fun w1 : M => v1 w1 z0))
  have v3 : (∀ z0 : M, (e15 z0)) := (show (∀ z0 : M, (e15 z0)) from v2)
  exact v3
-- Actual MMB 711 sbseqd
theorem p712 (a1 : M) (a2 : M → (M → Prop)) (a3 : M → (M → Prop)) (h0 : (g851 (M := M) a1 a2 a3 )) : (∀ z0 : M, (g852 (M := M) a1 a2 a3 z0)) := by
  let e0  : (M → Prop) := (t25 (M := M) (a1) (fun x0_1 : M => (a2 x0_1)))
  let e1 (u0 : M) : Prop := (t16 (M := M) u0 (e0))
  let e2 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a2 u1))
  let e3 (u0 : M) : Prop := (t14 (M := M) (a1) (fun x0_1 : M => (e2 u0 x0_1)))
  let e4 (u0 : M) : Prop := (t3 (e1 u0) (e3 u0))
  let e5 (u0 : M) (u1 : M) : Prop := (t16 (M := M) u0 (a3 u1))
  let e6 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e5 u0 x0_0)))
  let e7 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e8 (u0 : M) (u1 : M) : Prop := (t3 (e2 u0 u1) (e5 u0 u1))
  let e9 (u0 : M) (u1 : M) : Prop := (t0 (e7 u1) (e8 u0 u1))
  let e10 (u0 : M) : Prop := (t8 (M := M) (fun x0_0 : M => (e9 u0 x0_0)))
  let e11 (u0 : M) (u1 : M) : Prop := (t3 (e3 u0) (e5 u0 u1))
  let e12 (u0 : M) (u1 : M) : Prop := (t0 (e10 u0) (e11 u0 u1))
  let e13 (u0 : M) : Prop := (t17 (M := M) (a2 u0) (a3 u0))
  let e14 (u0 : M) (u1 : M) : Prop := (t0 (e13 u1) (e8 u0 u1))
  let e15 (u0 : M) : Prop := (t0 (e7 u0) (e13 u0))
  let e16 (u0 : M) (u1 : M) : Prop := (t0 (e15 u1) (e9 u0 u1))
  let e17 (u0 : M) (u1 : M) : Prop := (t0 (e14 u0 u1) (e16 u0 u1))
  let e18  : Prop := (t8 (M := M) (fun x0_0 : M => (e15 x0_0)))
  let e19 (u0 : M) : Prop := (t0 (e18) (e10 u0))
  let e20 (u0 : M) (u1 : M) : Prop := (t0 (e18) (e11 u0 u1))
  let e21 (u0 : M) (u1 : M) : Prop := (t3 (e1 u0) (e5 u0 u1))
  let e22 (u0 : M) (u1 : M) : Prop := (t0 (e18) (e21 u0 u1))
  let e23 (u0 : M) : Prop := (t17 (M := M) (e0) (a3 u0))
  let e24 (u0 : M) : Prop := (t0 (e18) (e23 u0))
  have v0 : (∀ z0 : M, (e4 z0)) := fun z0 : M => p703 (M := M) (fun w0 : M => (a1)) z0 (fun w0 : M => (a2 w0)) 0
  have v1 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p677 (M := M) z0 (fun w0 : M => (a3 w0)) (h0)
  have v2 : (∀ z0 : M, (∀ z1 : M, (e12 z0 z1))) := fun z0 : M => fun z1 : M => p525 (M := M) (a1) (fun w0 : M => (e2 z0 w0)) (fun w0 : M => (e5 z0 w0)) (v1 z0) z1
  have v3 : (∀ z0 : M, (∀ z1 : M, (e17 z0 z1))) := fun z0 : M => fun z1 : M => p19 (e7 z1) (e13 z1) (e8 z0 z1)
  have v4 : (∀ z0 : M, (∀ z1 : M, (e14 z0 z1))) := fun z0 : M => fun z1 : M => p573 (M := M) (a2 z1) (a3 z1) z0
  have v5 : (∀ z0 : M, (∀ z1 : M, (e16 z0 z1))) := fun z0 : M => fun z1 : M => b3 (e14 z0 z1) (e16 z0 z1) (v3 z0 z1) (v4 z0 z1)
  have v6 : (∀ z0 : M, (e19 z0)) := fun z0 : M => p337 (M := M) (fun w0 : M => (e15 w0)) (fun w0 : M => (e9 z0 w0)) ((fun w0 : M => v5 z0 w0))
  have v7 : (∀ z0 : M, (∀ z1 : M, (e20 z0 z1))) := fun z0 : M => fun z1 : M => p10 (e18) (e10 z0) (e11 z0 z1) (v2 z0 z1) (v6 z0)
  have v8 : (∀ z0 : M, (∀ z1 : M, (e22 z0 z1))) := fun z0 : M => fun z1 : M => p157 (e18) (e1 z0) (e3 z0) (e5 z0 z1) (v0 z0) (v7 z0 z1)
  have v9 : (∀ z0 : M, (e24 z0)) := fun z0 : M => p587 (M := M) (e0) (a3 z0) (e18) ((fun w3 : M => v8 w3 z0))
  exact v9
-- Actual MMB 713 sbsco
theorem p714 (a1 : M) (a2 : M → (M → Prop)) (a3 : M → (M → Prop)) (h0 : (g851 (M := M) a1 a2 a3 )) (h1 : (∀ z0 : M, (g854 (M := M) a1 a2 a3 z0))) : (∀ z0 : M, (g855 (M := M) a1 a2 a3 z0)) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : Prop := (t17 (M := M) (a2 u0) (a3 u0))
  let e2 (u0 : M) : Prop := (t0 (e0 u0) (e1 u0))
  let e3  : Prop := (t8 (M := M) (fun x0_0 : M => (e2 x0_0)))
  let e5 (u0 : M) : Prop := (t17 (M := M) ((show (M → Prop) from (t25 (M := M) (a1) (fun x0_1 : M => (a2 x0_1))))) (a3 u0))
  let e6 (u0 : M) : Prop := (t0 (e3) (e5 u0))
  have v0 : (∀ z0 : M, (e6 z0)) := fun z0 : M => p712 (M := M) (a1) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3 w0)) (h0) z0
  have v1 : (e3) := b325 (M := M) (fun w0 : M => (e2 w0)) ((fun w0 : M => h1 w0))
  have v2 : (∀ z0 : M, (e5 z0)) := fun z0 : M => b3 (e3) (e5 z0) (v0 z0) (v1)
  exact v2
-- Actual MMB 715 sbset
theorem p716 (a1 : M) (a2 : M → (M → Prop)) (a3 : (M → Prop)) (h0 : (∀ z0 : M, (g857 (M := M) a1 a2 a3 z0))) : (g858 (M := M) a1 a2 a3 ) := by
  have v0 : ((show Prop from (t23 (M := M) (fun x0_0 : M => (a3))))) := p673 (M := M) (a3)
  have v1 : ((show Prop from (t17 (M := M) ((show (M → Prop) from (t25 (M := M) (a1) (fun x0_1 : M => (a2 x0_1))))) (a3)))) := p714 (M := M) (a1) (fun w0 : M => (a2 w0)) (fun w0 : M => (a3)) (v0) ((fun w0 : M => h0 w0)) 0
  exact v1
-- Actual MMB 717 sbsed
theorem p737   : (g885 (M := M)  ) := by
  let e0  : M := (t28 (M := M))
  let e4  : Prop := (t13 (M := M) ((show M from (t30 (M := M)))) (e0))
  have v0 : ((show Prop from (t13 (M := M) ((show M from (t29 (M := M) (e0)))) (e0)))) := b734 (M := M) (e0)
  have v1 : (e4) := (show (e4) from v0)
  exact v1
-- Actual MMB 738 d2ne0
theorem p738   : (g886 (M := M)  ) := by
  let e0  : M := (t30 (M := M))
  let e2  : M := (t28 (M := M))
  let e5  : Prop := (t13 (M := M) ((show M from (t31 (M := M)))) (e2))
  have v0 : ((show Prop from (t13 (M := M) ((show M from (t29 (M := M) (e0)))) (e2)))) := b734 (M := M) (e0)
  have v1 : (e5) := (show (e5) from v0)
  exact v1
-- Actual MMB 739 suceq
theorem p739 (a0 : M) (a1 : M)  : (g887 (M := M) a0 a1 ) := by
  let e2  : Prop := (t10 (M := M) ((show M from (t29 (M := M) (a0)))) ((show M from (t29 (M := M) (a1)))))
  let e3  : Prop := (t10 (M := M) (a0) (a1))
  let e4  : Prop := (t3 (e2) (e3))
  let e5  : Prop := (t0 (e3) (e2))
  have v0 : ((show Prop from (t0 (e4) (e5)))) := p108 (e2) (e3)
  have v1 : (e4) := b735 (M := M) (a0) (a1)
  have v2 : (e5) := b3 (e4) (e5) (v0) (v1)
  exact v2
-- Actual MMB 740 suceqd
theorem p740 (a0 : Prop) (a1 : M) (a2 : M) (h0 : (g364 (M := M) a0 a1 a2 )) : (g888 (M := M) a0 a1 a2 ) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  let e3  : Prop := (t10 (M := M) ((show M from (t29 (M := M) (a1)))) ((show M from (t29 (M := M) (a2)))))
  have v0 : ((show Prop from (t0 (e0) (e3)))) := p739 (M := M) (a1) (a2)
  have v1 : ((show Prop from (t0 (a0) (e3)))) := p10 (a0) (e0) (e3) (v0) (h0)
  exact v1
-- Actual MMB 741 ind
theorem p741 (e : Nat → M) (a2 : M → M) (a3 : M → Prop) (a4 : M → Prop) (a5 : M → Prop) (a6 : M → Prop) (a7 : M → Prop) (certificate : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => a3 (v 0))) (h0 : (∀ z0 : M, (∀ z1 : M, (g889 (M := M) a2 a3 a4 a5 a6 a7 z0 z1)))) (h1 : (∀ z0 : M, (∀ z1 : M, (g890 (M := M) a2 a3 a4 a5 a6 a7 z0 z1)))) (h2 : (∀ z0 : M, (∀ z1 : M, (g891 (M := M) a2 a3 a4 a5 a6 a7 z0 z1)))) (h3 : (∀ z0 : M, (∀ z1 : M, (g892 (M := M) a2 a3 a4 a5 a6 a7 z0 z1)))) (h4 : (∀ z0 : M, (g893 (M := M) a2 a3 a4 a5 a6 a7 z0))) (h5 : (∀ z0 : M, (g894 (M := M) a2 a3 a4 a5 a6 a7 z0))) : (∀ z0 : M, (g895 (M := M) a2 a3 a4 a5 a6 a7 z0)) := by
  let e0  : Prop := (t8 (M := M) (fun x0_0 : M => (a3 x0_0)))
  let e1 (u0 : M) : Prop := (t0 (e0) (a5 u0))
  let e2  : M := (t28 (M := M))
  let e3  : Prop := (t14 (M := M) (e2) (fun x0_1 : M => (a3 x0_1)))
  let e4 (u0 : M) : M := (t29 (M := M) u0)
  let e5 (u0 : M) : Prop := (t14 (M := M) (e4 u0) (fun x0_1 : M => (a3 x0_1)))
  let e6 (u0 : M) : Prop := (t0 (a3 u0) (e5 u0))
  let e7  : Prop := (t8 (M := M) (fun x0_0 : M => (e6 x0_0)))
  let e8  : Prop := (t0 (e7) (e0))
  let e10 (u0 : M) : Prop := (t3 (e3) (a4 u0))
  let e11 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e6 u0)))
  let e12 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (a6 u0)))
  let e13 (u0 : M) : M := (t29 (M := M) u0)
  let e14 (u0 : M) : Prop := (t14 (M := M) (e13 u0) (fun x0_1 : M => (a3 x0_1)))
  let e15 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e14 u0)))
  let e16 (u0 : M) : Prop := (t0 (a6 u0) (e14 u0))
  let e17 (u0 : M) : Prop := (t11 (M := M) (fun x0_0 : M => (e16 u0)))
  let e18 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e19 (u0 : M) (u1 : M) : Prop := (t10 (M := M) (e4 u0) (e13 u1))
  let e20 (u0 : M) (u1 : M) : Prop := (t0 (e18 u0 u1) (e19 u0 u1))
  let e21 (u0 : M) (u1 : M) : Prop := (t3 (e5 u0) (e14 u1))
  let e22 (u0 : M) (u1 : M) : Prop := (t0 (e18 u0 u1) (e21 u0 u1))
  let e23 (u0 : M) (u1 : M) : Prop := (t3 (e6 u0) (e16 u1))
  let e24 (u0 : M) (u1 : M) : Prop := (t0 (e18 u0 u1) (e23 u0 u1))
  let e25  : Prop := (t8 (M := M) (fun x0_0 : M => (e16 x0_0)))
  let e27 (u0 : M) : Prop := (t3 (e14 u0) (a7 u0))
  let e28 (u0 : M) : Prop := (t0 (a7 u0) (e14 u0))
  have v0 : (∀ z0 : M, (e1 z0)) := fun z0 : M => p440 (M := M) (a2 z0) (fun w0 : M => (a3 w0)) (a5 z0) ((fun w0 : M => h0 w0 z0))
  have v1 : ((show Prop from (t0 (e3) (e8)))) := b736 (M := M) (fun w0 : M => (a3 w0)) e certificate
  have v2 : (∀ z0 : M, (e10 z0)) := fun z0 : M => p528 (M := M) (e2) (fun w0 : M => (a3 w0)) (a4 z0) ((fun w0 : M => h1 w0 z0))
  have v3 : (e3) := p118 (a4 0) (e3) (v2 0) (h4 0)
  have v4 : (e8) := b3 (e3) (e8) (v1) (v3)
  have v5 : (∀ z0 : M, (e11 z0)) := fun z0 : M => p405 (M := M) (e6 z0)
  have v6 : (∀ z0 : M, (e12 z0)) := fun z0 : M => p405 (M := M) (a6 z0)
  have v7 : (∀ z0 : M, (e15 z0)) := fun z0 : M => p518 (M := M) (e13 z0) (fun w0 : M => (a3 w0))
  have v8 : (∀ z0 : M, (e17 z0)) := fun z0 : M => p412 (M := M) (fun w0 : M => (a6 z0)) (fun w0 : M => (e14 z0)) (v6 z0) (v7 z0)
  have v9 : (∀ z0 : M, (∀ z1 : M, (e20 z0 z1))) := fun z0 : M => fun z1 : M => p739 (M := M) z0 z1
  have v10 : (∀ z0 : M, (∀ z1 : M, (e22 z0 z1))) := fun z0 : M => fun z1 : M => p521 (M := M) (fun w0 : M => (e18 w0 z1)) (fun w0 : M => (e4 w0)) (fun w0 : M => (e13 z1)) (fun w0 : M => (a3 w0)) ((fun w0 : M => v9 w0 z1)) z0
  have v11 : (∀ z0 : M, (∀ z1 : M, (e24 z0 z1))) := fun z0 : M => fun z1 : M => p188 (e18 z0 z1) (a3 z0) (a6 z1) (e5 z0) (e14 z1) (h2 z0 z1) (v10 z0 z1)
  have v12 : ((show Prop from (t3 (e7) (e25)))) := p480 (M := M) (fun w0 : M => (fun w1 : M => (e6 w0))) (fun w0 : M => (fun w1 : M => (e16 w1))) ((fun w0 : M => v5 w0)) ((fun w1 : M => v8 w1)) ((fun w0 : M => (fun w1 : M => v11 w0 w1))) 0 0
  have v13 : (∀ z0 : M, (e27 z0)) := fun z0 : M => p528 (M := M) (e13 z0) (fun w0 : M => (a3 w0)) (a7 z0) ((fun w0 : M => h3 w0 z0))
  have v14 : (∀ z0 : M, (e28 z0)) := fun z0 : M => p109 (e14 z0) (a7 z0) (v13 z0)
  have v15 : (∀ z0 : M, (e16 z0)) := fun z0 : M => p11 (a6 z0) (a7 z0) (e14 z0) (h5 z0) (v14 z0)
  have v16 : (e25) := b325 (M := M) (fun w0 : M => (e16 w0)) ((fun w0 : M => v15 w0))
  have v17 : (e7) := p118 (e25) (e7) (v12) (v16)
  have v18 : (e0) := b3 (e7) (e0) (v4) (v17)
  have v19 : (∀ z0 : M, (a5 z0)) := fun z0 : M => b3 (e0) (a5 z0) (v0 z0) (v18)
  exact v19
end ZF207.MM0ModelReplay
