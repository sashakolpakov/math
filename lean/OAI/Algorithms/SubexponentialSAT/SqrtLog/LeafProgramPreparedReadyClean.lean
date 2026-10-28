import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyNode

namespace OAI.Algorithms

/-! Uniform blank-port facts supplied by the actual node preparation. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls NodeNative LeafHeadSetupProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def blankPort (i : Fin 768) : Prop :=
  (56 ≤ i.val ∧ i.val < 96 ∧ i ∉ ([69,76,78,88] : List (Fin 768))) ∨
  (143 ≤ i.val ∧ i.val < 160 ∧ i≠143) ∨
  (340 ≤ i.val ∧ i.val ≤ 684)
instance : DecidablePred blankPort := fun _=>inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem preparation_blank {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a)
    (i : Fin 768) (hi : blankPort i) : b.stacks i=[] := by
  have hn : i≠78 ∧ i≠69 ∧ i≠76 ∧ i≠88 ∧ i≠143 := by
    refine ⟨?_,?_,?_,?_,?_⟩ <;> intro he <;> subst i <;> norm_num [blankPort] at hi
  apply pr.empty_word ha
  · apply (Node.mem_cleanup i).mpr
    rcases hi with hi|hi|hi <;> omega
  · intro hm
    obtain ⟨j,_,he⟩ := List.mem_map.mp hm
    have hv := congrArg Fin.val he
    change 128+j.val=i.val at hv
    have hj := j.isLt
    rcases hi with hi|hi|hi <;> omega
  · intro hm
    simp only [LeafNodeCacheProgram.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp_all [blankPort]
  · intro hm
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all [blankPort]

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
