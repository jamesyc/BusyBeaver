module
public import DirectRoutineRelabel
public import DirectFramedRowEquality
@[expose] public section
namespace RosserDirect.RowPairEquality
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Control where
 | first (q : FramedRowEquality.Control)
 | second (q : FramedRowEquality.Control)
 | equal | different
 deriving DecidableEq, Fintype, Inhabited

def machine : Control → Stmt Control
 | .first .equal => .goto (fun _ => .second .tag)
 | .first .different => .goto (fun _ => .different)
 | .first q => Routine.relocate id Control.first (FramedRowEquality.machine q)
 | .second .equal => .goto (fun _ => .equal)
 | .second .different => .goto (fun _ => .different)
 | .second q => Routine.relocate id Control.second (FramedRowEquality.machine q)
 | .equal | .different => .halt

theorem agree_first (q : FramedRowEquality.Control) (h : FramedRowEquality.machine q ≠ .halt) :
 machine (.first q) = Routine.relocate id Control.first (FramedRowEquality.machine q) := by
 cases q <;> simp_all [machine,FramedRowEquality.machine,FramedRowEquality.active]
theorem agree_second (q : FramedRowEquality.Control) (h : FramedRowEquality.machine q ≠ .halt) :
 machine (.second q) = Routine.relocate id Control.second (FramedRowEquality.machine q) := by
 cases q <;> simp_all [machine,FramedRowEquality.machine,FramedRowEquality.active]

theorem embed_first (q : FramedRowEquality.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.first (config q v a b c) (fun _ => []) = config (.first q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_second (q : FramedRowEquality.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.second (config q v a b c) (fun _ => []) = config (.second q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

abbrev rows (r₁ r₂ : ZFR.Row) := FramedRow.encode r₁ ++ FramedRow.encode r₂

theorem equal_pairs (r₁ r₂ : ZFR.Row) (v : Option Symbol) (src scr dst : List Symbol) :
 ∃ w, TM2.Reaches machine
 (config (.first .tag) v (rows r₁ r₂ ++ src) scr (rows r₁ r₂ ++ dst))
 (config .equal w src scr dst) := by
 obtain ⟨w,h⟩ := FramedRowEquality.equal_rows_exact r₁ v (FramedRow.encode r₂ ++ src) scr (FramedRow.encode r₂ ++ dst)
 have hf := Routine.lift_embedded_run id Function.injective_id Control.first FramedRowEquality.machine machine agree_first (fun _ => []) h (by simp [config])
 simp only [embed_first] at hf
 have hl : TM2.Reaches machine
   (config (.first .equal) w (FramedRow.encode r₂ ++ src) scr (FramedRow.encode r₂ ++ dst))
   (config (.second .tag) w (FramedRow.encode r₂ ++ src) scr (FramedRow.encode r₂ ++ dst)) := Relation.ReflTransGen.single rfl
 obtain ⟨z,h⟩ := FramedRowEquality.equal_rows_exact r₂ w src scr dst
 have hs := Routine.lift_embedded_run id Function.injective_id Control.second FramedRowEquality.machine machine agree_second (fun _ => []) h (by simp [config])
 simp only [embed_second] at hs
 have he : TM2.Reaches machine (config (.second .equal) z src scr dst) (config .equal z src scr dst) := Relation.ReflTransGen.single rfl
 refine ⟨z,?_⟩
 simpa [TM2.Reaches,rows,List.append_assoc] using hf.trans (hl.trans (hs.trans he))

theorem different_pairs (r₁ r₂ t₁ t₂ : ZFR.Row) (hne : ¬(r₁ = t₁ ∧ r₂ = t₂))
 (v : Option Symbol) (src scr dst : List Symbol) :
 ∃ w left right, TM2.Reaches machine
 (config (.first .tag) v (rows r₁ r₂ ++ src) scr (rows t₁ t₂ ++ dst))
 (config .different w left scr right) := by
 by_cases hfirst : r₁ = t₁
 · subst t₁
   have hn : r₂ ≠ t₂ := by intro h; exact hne ⟨rfl,h⟩
   obtain ⟨w,h⟩ := FramedRowEquality.equal_rows_exact r₁ v (FramedRow.encode r₂ ++ src) scr (FramedRow.encode t₂ ++ dst)
   have hf := Routine.lift_embedded_run id Function.injective_id Control.first FramedRowEquality.machine machine agree_first (fun _ => []) h (by simp [config])
   simp only [embed_first] at hf
   have hl : TM2.Reaches machine
     (config (.first .equal) w (FramedRow.encode r₂ ++ src) scr (FramedRow.encode t₂ ++ dst))
     (config (.second .tag) w (FramedRow.encode r₂ ++ src) scr (FramedRow.encode t₂ ++ dst)) := Relation.ReflTransGen.single rfl
   obtain ⟨z,left,right,h⟩ := FramedRowEquality.compare_rows r₂ t₂ w src scr dst
   simp only [hn,↓reduceIte] at h
   have hs := Routine.lift_embedded_run id Function.injective_id Control.second FramedRowEquality.machine machine agree_second (fun _ => []) h (by simp [config])
   simp only [embed_second] at hs
   have he : TM2.Reaches machine (config (.second .different) z left scr right) (config .different z left scr right) := Relation.ReflTransGen.single rfl
   refine ⟨z,left,right,?_⟩
   simpa [TM2.Reaches,rows,List.append_assoc] using hf.trans (hl.trans (hs.trans he))
 · obtain ⟨w,left,right,h⟩ := FramedRowEquality.compare_rows r₁ t₁ v (FramedRow.encode r₂ ++ src) scr (FramedRow.encode t₂ ++ dst)
   simp only [hfirst,↓reduceIte] at h
   have hf := Routine.lift_embedded_run id Function.injective_id Control.first FramedRowEquality.machine machine agree_first (fun _ => []) h (by simp [config])
   simp only [embed_first] at hf
   have he : TM2.Reaches machine (config (.first .different) w left scr right) (config .different w left scr right) := Relation.ReflTransGen.single rfl
   refine ⟨w,left,right,?_⟩
   simpa [TM2.Reaches,rows,List.append_assoc] using hf.trans he

end RosserDirect.RowPairEquality
