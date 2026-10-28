import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeFinishReplay

/-! The complete streamed recovery command does not inspect or modify the
marked-record cursor320 or accumulated mass322. This includes the paid jet
handoff, actual scratch preparation, the CRT, canonical reader and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstructionReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

private theorem bankClear_avoids {r s : ℕ} (H : Fin s → Prop)
    (temporary : Fin s) (value present : Fin r) (ports : List (Fin s))
    (ht : ¬ H temporary) (hp : ∀ i ∈ ports, ¬ H i) :
    AvoidsCmd H (BankRoutines.clearCmd temporary value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram H temporary value present ht
  | cons i ports ih =>
      exact ⟨avoids_clearProgram H i value present (hp i (by simp)),
        ih (fun j hj => hp j (by simp [hj]))⟩

theorem prepare_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      SqrtLog.LeafProgram.Count.Prepare.command := by
  unfold SqrtLog.LeafProgram.Count.Prepare.command
  generalize hports : SqrtLog.LeafProgram.Count.Prepare.ports = ports
  refine ⟨avoids_clearProgram _ 699 0 1 (by decide),
    bankClear_avoids _ 699 0 1 ports (by decide) ?_⟩
  intro i hi hidden
  rw [← hports] at hi
  exact (QueryReconstruction.collector_outside i (by omega) (by omega)) hi

theorem core_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      QueryReconstruction.coreCommand :=
  ⟨prepare_avoids, ReconstructionReplay.command_avoids⟩

theorem core_lift_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      (liftCommand QueryReconstruction.coreCommand 256 323 id (Fin.castAdd 128)) := by
  apply avoids_liftProgram
  exact avoids_compiled _ _ core_avoids 256 323

theorem command_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      QueryReconstruction.command :=
  ⟨NodeFinishReplay.handoff_avoids, core_lift_avoids⟩

theorem program_avoids :
    AvoidsProgram (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      QueryReconstruction.program :=
  avoids_compiled _ _ command_avoids 863 323

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstructionReplay
