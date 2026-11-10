import PA215.Source.ContractPlan
import PA215.Source.ObligationKeys
namespace PA215.Source.ObligationKeys
open PA215.Runtime PA215.Census

def branchBit : Branch → Nat
  | some (_,false) => 1
  | _ => 0

def rawKey (r : RawOriginal) : Nat := 2*r.siteIndex + branchBit r.branch

def keyOf (i : Nat) : Op → Bool → Nat
  | .dec _,false => 2*i+1
  | _,_ => 2*i

def expectedBranch : Op → Bool → Branch
  | .dec r,z => some (physicalRegister r,z)
  | _,_ => none

def Compatible : Op → Branch → Prop
  | .dec r,br => ∃ z, br = some (physicalRegister r,z)
  | _,br => br = none

theorem keyOf_member (i : Nat) (op : Op) (z : Bool) : keyOf i op z ∈ atSite i op := by
  cases op <;> cases z <;> simp [keyOf,atSite]

theorem bit_le (br : Branch) : branchBit br ≤ 1 := by
  cases br with
  | none => decide
  | some p => rcases p with ⟨r,b⟩; cases b <;> simp [branchBit]

theorem key_bounds (i : Nat) (op : Op) (z : Bool) :
    2*i ≤ keyOf i op z ∧ keyOf i op z ≤ 2*i+1 := by
  cases op <;> cases z <;> simp [keyOf]

theorem key_index (r : RawOriginal) (i : Nat) (op : Op) (z : Bool)
    (hk : rawKey r = keyOf i op z) : r.siteIndex = i := by
  have hb := bit_le r.branch
  have hs := key_bounds i op z
  unfold rawKey at hk
  omega

theorem compatible_of_plan (s : Site) (br : Branch) (hp : targetPlan s br ≠ none) :
    Compatible s.op br := by
  cases hs : s.op with
  | dec v =>
    cases br with
    | none => simp [targetPlan,hs] at hp
    | some p =>
      rcases p with ⟨r,b⟩
      by_cases he : r = physicalRegister v
      · exact ⟨b,by simp [he]⟩
      · simp [targetPlan,hs,he] at hp
  | inc v => cases br <;> simp_all [targetPlan,Compatible]
  | breakTo n => cases br <;> simp_all [targetPlan,Compatible]
  | continueTo n => cases br <;> simp_all [targetPlan,Compatible]
  | halt => cases br <;> simp_all [targetPlan,Compatible]

theorem key_branch (r : RawOriginal) (s : Site) (i : Nat) (z : Bool)
    (hc : Compatible s.op r.branch) (hk : rawKey r = keyOf i s.op z) :
    r.branch = expectedBranch s.op z := by
  have hi := key_index r i s.op z hk
  cases hs : s.op with
  | dec v =>
    simp only [hs,Compatible] at hc
    obtain ⟨b,hb⟩ := hc
    rw [rawKey,hi,hb,hs] at hk
    cases b <;> cases z <;> simp_all [branchBit,keyOf,expectedBranch]
  | inc v => simpa [hs,Compatible,expectedBranch] using hc
  | breakTo n => simpa [hs,Compatible,expectedBranch] using hc
  | continueTo n => simpa [hs,Compatible,expectedBranch] using hc
  | halt => simpa [hs,Compatible,expectedBranch] using hc


/-- A key-list equality supplies actual original records for each source branch;
metadata compatibility recovers the physical register, not just a numeric ID. -/
theorem coverage (sites : List Site) (rs : List RawOriginal)
    (hkeys : rs.map rawKey = required 0 sites)
    (hcompatible : ∀ r ∈ rs, ∃ s, sites[r.siteIndex]? = some s ∧ Compatible s.op r.branch)
    (i : Nat) (s : Site) (z : Bool) (hs : sites[i]? = some s) :
    ∃ r ∈ rs, r.siteIndex = i ∧ r.branch = expectedBranch s.op z := by
  have hm : keyOf i s.op z ∈ required 0 sites := by
    apply required_member sites 0 i s hs
    simpa only [Nat.zero_add] using keyOf_member i s.op z
  rw [← hkeys] at hm
  obtain ⟨r,hr,hkey⟩ := List.mem_map.mp hm
  have hi := key_index r i s.op z hkey
  obtain ⟨s',hs',hc⟩ := hcompatible r hr
  rw [hi,hs] at hs'
  have he : s = s' := Option.some.inj hs'
  subst s'
  exact ⟨r,hr,hi,key_branch r s i z hc hkey⟩

#print axioms key_branch
#print axioms coverage
end PA215.Source.ObligationKeys
