import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeUniform

namespace OAI.Algorithms

/-! Bounds exclude the seven opaque buffers owned by the indexed collector. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
open SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

def carriedPorts : List (Fin 768) := [256,265,301,302,303,304,305]
def LocalWordBound (B : ℕ) (a : NodeNative.Data) : Prop :=
  ∀ i,i∉carriedPorts → (a.stacks i).length ≤ B

theorem loaded_localWordBound {s : HeadInputs} {a : NodeNative.Data} (ha : Ready s a)
    (B : ℕ) (hb : LocalWordBound B a) : LocalWordBound B (loadedState a) := by
  intro i hni
  by_cases hi : i∈LayoutMasters.lowPorts
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    have hh := LayoutMasters.loaded_low (LayoutMasters.project a)
      (fun j=>ha.blank _ (low_mem_cleanup j) (by
        intro he; have hv := congrArg Fin.val he
        change 128+j.val=78 at hv
        omega)) j
    change ((LayoutMasters.loaded (LayoutMasters.project a)).stacks (LayoutMasters.low j)).length ≤ B
    rw [hh]
    apply hb
    intro h
    simp only [carriedPorts,List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with h|h|h|h|h|h|h <;>
      have hv := congrArg Fin.val h <;>
      change 730+j.val=_ at hv <;> norm_num at hv <;> omega
  · change ((LayoutMasters.loaded (LayoutMasters.project a)).stacks i).length ≤ B
    rw [LayoutMasters.loaded_frame (LayoutMasters.project a) i hi]
    exact hb _ hni

theorem local_loadCost_le {s : HeadInputs} {a : NodeNative.Data} (_ha : Ready s a)
    (B : ℕ) (hb : LocalWordBound B a) :
    LayoutMasters.loadCost (LayoutMasters.project a) ≤ 14*(7*B+5) := by
  apply LayoutMasters.loadCost_le
  intro j
  apply hb
  intro h
  simp only [carriedPorts,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with h|h|h|h|h|h|h <;>
    have hv := congrArg Fin.val h <;>
    change 730+j.val=_ at hv <;> norm_num at hv <;> omega

theorem Preparation.local_cache_budget_le {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) (B : ℕ) (hb : LocalWordBound B a) :
    LeafNodeCacheProgram.budget pr.headEnd ≤ 1001*(B+1) := by
  have hl := loaded_localWordBound ha B hb
  apply cache_budget_le_sources
  intro q hq
  have hs : External q.1 ∧ q.1∉carriedPorts := by
    simp only [LeafNodeCacheProgram.copies,LeafNodeCacheProgram.directCopies,
      List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hq
    rcases hq with hq|hq
    · rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        norm_num [External,Fin.ext_iff,carriedPorts]
    · rcases hq with rfl|rfl <;> norm_num [External,Fin.ext_iff,carriedPorts]
  rw [pr.head.frame _ hs.1,pr.loaded_words]
  exact hl _ hs.2

theorem carried_disjoint_cleanup (i : Fin 768) (hi : i∈Node.cleanupPorts) : i∉carriedPorts := by
  intro h
  simp only [carriedPorts,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [Node.mem_cleanup] at hi

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms
