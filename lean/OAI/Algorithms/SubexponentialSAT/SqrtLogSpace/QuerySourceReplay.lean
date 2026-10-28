import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramIncidence
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram

/-! Actual source-emitter reads and writes exclude the two collector tapes.
The exclusion includes staging, restoration, arithmetic calls and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceReplay

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

local notation "H" => (fun i : Fin 768 => Fin.val i = 320 ∨ Fin.val i = 322)

theorem high_port (i : Fin 768) (hi : 340 ≤ i.val) : ¬ H i := by omega

theorem source_before_avoids : AvoidsCmd H SourceStaging.before := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_, avoids_clearMany _ _ ?_⟩
  · simp [SourceStaging.savePairs]
  · simp [SourceStaging.cachePorts]

theorem source_after_avoids : AvoidsCmd H SourceStaging.after := by
  refine ⟨avoids_clearMany _ _ ?_, avoids_copyMany _ _ _ (by decide) ?_,
    avoids_clearMany _ _ ?_, avoids_clearMany _ _ ?_⟩
  · simp [SourceStaging.cachePorts]
  · simp [SourceStaging.restorePairs]
  · simp [SourceStaging.backupPorts]
  · intro i hi
    obtain ⟨j, _, rfl⟩ := (SourceStaging.lowClear_iff i).mp hi
    exact high_port _ (by change 340 ≤ 340 + j.val; omega)

theorem source_prepare_avoids : AvoidsCmd H SourceControls.prepare := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_, True.intro, ?_⟩
  · simp [SourceControls.pairs]
  · change ¬ H 365
    decide

theorem source_cleanup_avoids : AvoidsCmd H SourceControls.cleanup := by
  apply avoids_clearMany
  intro i hi
  have hh := (SourceControls.mem_extraPorts i).mp hi
  exact high_port i (by omega)

theorem source_avoids : AvoidsCmd H Source.command := by
  refine ⟨source_before_avoids, source_prepare_avoids, ?_,
    source_after_avoids, source_cleanup_avoids⟩
  apply avoids_call_lift_of_range
  intro i
  exact high_port _ (by change 340 ≤ 340 + i.val; omega)

theorem stage_avoids : AvoidsCmd H Incidence.stage := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_,
    avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide), True.intro, ?_⟩
  · simp [Incidence.pairs]
  · change ¬ H 550
    decide

theorem export_avoids : AvoidsCmd H Incidence.exportResult := by
  refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide),
    avoids_clearMany _ _ ?_⟩
  intro i hi
  exact high_port i ((Incidence.mem_workerPorts i).mp hi).1

namespace Table
open FactorTableProgram
local notation "HW" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322)

theorem base_predicate (i : Fin 768) : HW (basePort i) ↔ H i := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem base_high (i : Fin 768) (hi : 340 ≤ i.val) : 340 ≤ (basePort i).val := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.coe_ofNat_eq_mod]

theorem lift_base_avoids (c : Cmd 16 768) (hc : AvoidsCmd H c) :
    AvoidsCmd HW (liftBase c) := by
  apply avoids_liftProgram
  have hp : (fun i : Fin 768 => HW (basePort i)) = H := by
    funext i
    exact propext (base_predicate i)
  change AvoidsProgram (fun i : Fin 768 => HW (basePort i)) (compiled c 0 0)
  rw [hp]
  exact avoids_compiled _ _ hc _ _

theorem inner_avoids (c : Cmd 16 256) :
    AvoidsCmd HW (liftInner c) := by
  apply avoids_liftCommand_of_range
  intro i
  change ¬ (340+i.val=320 ∨ 340+i.val=322)
  omega

theorem specialize_avoids : AvoidsCmd HW specializeCall := by
  refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide), ?_⟩
  apply avoids_liftCommand_of_range
  intro i
  change ¬ (340+i.val=320 ∨ 340+i.val=322)
  omega

theorem low_payload_avoids : AvoidsCmd HW lowPayload :=
  ⟨lift_base_avoids _ source_avoids, specialize_avoids⟩

theorem literal_payload_avoids : AvoidsCmd HW literalPayload :=
  ⟨inner_avoids _, inner_avoids _, low_payload_avoids⟩

theorem literal_iteration_avoids : AvoidsCmd HW literalIteration :=
  ⟨inner_avoids _, literal_payload_avoids, inner_avoids _⟩

theorem prepare_factor_avoids : AvoidsCmd HW prepareFactor :=
  ⟨inner_avoids _, avoids_forCmd _ _ _ (by decide) literal_iteration_avoids,
    inner_avoids _⟩

theorem entry_avoids : AvoidsCmd HW initializeWorker := by
  apply avoids_clearMany
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hj' := (Incidence.mem_workerPorts j).mp (List.mem_filter.mp hj).1
    have hh := base_high j hj'.1
    omega
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Table

theorem command_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322) FactorTableProgram.command :=
  ⟨Table.entry_avoids, Table.lift_base_avoids _ stage_avoids,
    Table.prepare_factor_avoids, Table.lift_base_avoids _ export_avoids⟩

theorem program_avoids :
    AvoidsProgram (fun i : Fin 896 => i.val=320 ∨ i.val=322) FactorTableProgram.program :=
  avoids_compiled _ _ command_avoids _ _

theorem caller_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322) FactorTableProgram.caller :=
  avoids_liftProgram _ _ _ _ program_avoids

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceReplay
