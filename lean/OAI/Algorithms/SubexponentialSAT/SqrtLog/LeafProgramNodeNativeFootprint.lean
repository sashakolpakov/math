import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeReplayBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayFootprint

namespace OAI.Algorithms

/-! Structural no-read/no-write certificates for the node's owned stages. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
open SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod
attribute [local irreducible] Node.cleanup Node.cleanupPorts

private theorem copyMany_avoids (H : Fin 768 → Prop) (tmp : Fin 768)
    (ht : ¬H tmp) (ps : List (Fin 768 × Fin 768))
    (hp : ∀ p∈ps,¬H p.1 ∧ ¬H p.2) : AvoidsCmd H (copyMany tmp ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨avoids_copyProgram H p.1 p.2 tmp 0 1 (hp p (by simp)).1 (hp p (by simp)).2 ht,
      ih (fun p h=>hp p (by simp [h]))⟩

theorem load_avoids : AvoidsCmd collectorTape LayoutMasters.load := by
  apply avoids_liftProgram
  apply avoids_compiled
  apply copyMany_avoids
  · decide
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    fin_cases i <;> decide

theorem cache_local_avoids : AvoidsCmd collectorTape LeafNodeCacheProgram.localCommand := by
  change AvoidsCmd collectorTape LeafNodeCacheProgram.prepare ∧
    AvoidsCmd collectorTape LeafNodeCacheProgram.constant ∧
    AvoidsCmd collectorTape LeafNodeCacheProgram.duplicate ∧
    AvoidsCmd collectorTape LeafNodeCacheProgram.finish
  refine ⟨?_,?_,?_,?_⟩
  · apply copyMany_avoids
    · decide
    · simp [LeafNodeCacheProgram.copies,LeafNodeCacheProgram.directCopies,collectorTape,carriedPorts]
  · apply avoids_call_lift_of_range
    intro i; fin_cases i <;> decide
  · apply copyMany_avoids
    · decide
    · simp [collectorTape,carriedPorts]
  · exact avoids_clearProgram collectorTape 345 0 1 (by decide)

theorem cache_avoids : AvoidsCmd collectorTape LeafNodeCacheProgram.command := by
  apply avoids_liftProgram
  exact avoids_compiled _ _ cache_local_avoids _ _

theorem supports_avoids : AvoidsCmd collectorTape Node.supports := by
  apply avoids_compiled
  apply avoids_call_lift_of_range
  intro i; fin_cases i <;> decide

theorem clearList_avoids (ps : List (Fin 768)) (hp : ∀ i∈ps,¬collectorTape i) :
    AvoidsCmd collectorTape (Node.clearList ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨avoids_clearProgram collectorTape p 0 1 (hp p (by simp)),
      ih (fun i h=>hp i (by simp [h]))⟩

theorem cleanup_avoids : AvoidsCmd collectorTape Node.cleanup := by
  rw [Node.cleanup]
  exact clearList_avoids Node.cleanupPorts carried_disjoint_cleanup

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end OAI.Algorithms
