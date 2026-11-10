import PA213.SourceCheck
import PA213.PathBounds
namespace PA213.FastSourceCheck
open PA215.Source PA215.Source.PathTrie PA213.FastResolve PA213.SourceProgram

def check (base count : Nat) : Bool :=
  decide (((sites.toList.drop base).take count).map (resolveTree trie) =
    ((codes.toList.drop base).take count).map some) &&
  decide (((exactSites.toList.drop base).take count).map (resolveTree exactTrie) =
    ((codes.toList.drop base).take count).map some)

private theorem extract_resolve (ss : Array Site) (t : Tree) (cs : Array Instruction)
    (base count i : Nat) (lo : base ≤ i) (hi : i < base+count)
    (h : ((ss.toList.drop base).take count).map (resolveTree t) =
      ((cs.toList.drop base).take count).map some) :
    (ss[i]?).bind (resolveTree t) = cs[i]? := by
  have hh := congrArg (fun xs => xs[i-base]?) h
  have hb : i-base < count := by omega
  simp only [List.getElem?_map,List.getElem?_take_of_lt hb,List.getElem?_drop,
    Nat.add_sub_of_le lo,Array.getElem?_toList] at hh
  cases hs : ss[i]? <;> cases hc : cs[i]? <;> simp_all

theorem sound {base count : Nat} (h : check base count = true)
    (i : Nat) (lo : base ≤ i) (hi : i < base+count) : PA213.SourceCheck.atCheck i = true := by
  obtain ⟨hc,hb⟩ := Bool.and_eq_true_iff.mp h
  have hc' := extract_resolve sites trie codes base count i lo hi (of_decide_eq_true hc)
  have hb' := extract_resolve exactSites exactTrie codes base count i lo hi (of_decide_eq_true hb)
  simp only [PA213.SourceCheck.atCheck,hc',hb',beq_self_eq_true,Bool.true_and]
  exact decide_eq_true (PA213.PathBounds.path_short i)
end PA213.FastSourceCheck
