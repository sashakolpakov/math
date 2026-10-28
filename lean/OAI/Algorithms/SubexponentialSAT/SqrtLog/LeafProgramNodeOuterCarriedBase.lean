import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramOuterCarried
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayFootprint

namespace OAI.Algorithms

/-! Structural no-read/no-write certificates for the node's owned stages for the three outer caller tapes. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.OuterCarried
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
open SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem copyMany_avoids (H : Fin 768 → Prop) (tmp : Fin 768)
    (ht : ¬H tmp) (ps : List (Fin 768 × Fin 768))
    (hp : ∀ p∈ps,¬H p.1 ∧ ¬H p.2) : AvoidsCmd H (copyMany tmp ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨avoids_copyProgram H p.1 p.2 tmp 0 1 (hp p (by simp)).1 (hp p (by simp)).2 ht,
      ih (fun p h=>hp p (by simp [h]))⟩

theorem node_load_avoids : AvoidsCmd hidden LayoutMasters.load := by
  apply avoids_liftProgram
  apply avoids_compiled
  apply copyMany_avoids
  · decide
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    fin_cases i <;> decide

theorem node_cache_local_avoids : AvoidsCmd hidden LeafNodeCacheProgram.localCommand := by
  change AvoidsCmd hidden LeafNodeCacheProgram.prepare ∧
    AvoidsCmd hidden LeafNodeCacheProgram.constant ∧
    AvoidsCmd hidden LeafNodeCacheProgram.duplicate ∧
    AvoidsCmd hidden LeafNodeCacheProgram.finish
  refine ⟨?_,?_,?_,?_⟩
  · apply copyMany_avoids
    · decide
    · simp [LeafNodeCacheProgram.copies,LeafNodeCacheProgram.directCopies,hidden]
  · apply avoids_call_lift_of_range
    intro i; fin_cases i <;> decide
  · apply copyMany_avoids
    · decide
    · simp [hidden]
  · exact avoids_clearProgram hidden 345 0 1 (by decide)

theorem node_cache_avoids : AvoidsCmd hidden LeafNodeCacheProgram.command := by
  apply avoids_liftProgram
  exact avoids_compiled _ _ node_cache_local_avoids _ _

theorem node_supports_avoids : AvoidsCmd hidden Node.supports := by
  apply avoids_compiled
  apply avoids_call_lift_of_range
  intro i; fin_cases i <;> decide

theorem node_clearList_avoids (ps : List (Fin 768)) (hp : ∀ i∈ps,¬hidden i) :
    AvoidsCmd hidden (Node.clearList ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨avoids_clearProgram hidden p 0 1 (hp p (by simp)),
      ih (fun i h=>hp i (by simp [h]))⟩

theorem node_cleanup_avoids : AvoidsCmd hidden Node.cleanup :=
by
  generalize hps : Node.cleanupPorts = ps
  have hp : ∀ i∈ps,¬hidden i := by
    intro i hi hh
    have hn := (Node.mem_cleanup i).mp (by simpa only [hps] using hi)
    simp only [hidden,List.mem_cons,List.mem_nil_iff,or_false] at hh
    rcases hh with rfl|rfl|rfl <;> norm_num at hn
  have hclear : AvoidsCmd hidden (Node.clearList ps) :=
    node_clearList_avoids ps hp
  have hc : Node.clearList ps = Node.cleanup := by
    rw [Node.cleanup, hps]
  exact hc ▸ hclear

end SubexponentialSAT.SqrtLog.LeafProgram.OuterCarried

end OAI.Algorithms
