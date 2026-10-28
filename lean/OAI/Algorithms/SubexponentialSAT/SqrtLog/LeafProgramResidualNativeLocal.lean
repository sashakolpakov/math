import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeNode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeLocalBounds

namespace OAI.Algorithms

/-! The node size invariant does not constrain collector-owned streams. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls LeafNodeSamplesProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

 theorem collector_local_bound (regs : Fin 40 → Bool) (s : Store)
    (i B : ℕ) (node : List Bool)
    (hf : ∀ j,j∉NodeNative.carriedPorts → (s.frame j).length ≤ B)
    (hi : i ≤ B) (hn : node.length ≤ B)
    (hx : s.index=List.replicate i true) (hnode : s.node=node)
    (hj : s.jet=[]) (hs : s.shape=[]) :
    NodeNative.LocalWordBound B (state regs s) := by
  intro j hcarried
  by_cases h307 : j=307
  · subst j
    simpa only [state,tapes_index,hx,List.length_replicate] using hi
  by_cases h78 : j=78
  · subst j
    simpa only [state,tapes_node,hnode] using hn
  by_cases h102 : j=102
  · subst j
    simp only [state,tapes_jet,hj,List.length_nil,Nat.zero_le]
  by_cases h104 : j=104
  · subst j
    simp only [state,tapes_shape,hs,List.length_nil,Nat.zero_le]
  have hc : j∉collectorPorts := by
    intro hm
    simp only [collectorPorts,List.mem_cons,List.mem_nil_iff,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|h|h|h|h|rfl|rfl
    all_goals first | exact h307 h | exact h78 h | exact h102 h | exact h104 h |
      exact hcarried (by simp [NodeNative.carriedPorts])
  change (tapes s j).length ≤ B
  rw [collector_frame s j hc]
  exact hf j hcarried

end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
