import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayFootprint

/-! The actual CRT, canonical whole-word reader and paid cleanup never inspect
or modify the marked-record cursor320 or accumulated mass322. This syntactic
certificate supports exact-time replay while the caller still charges their
retained words in every prefix-space bound. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionReplay

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog ProgramTapeReplay

/-- Only the explicit eight scalar-reader ports can be touched. -/
theorem reader_avoids :
    AvoidsCmd (fun i : Fin 330 => i.val = 320 ∨ i.val = 322)
      ReconstructionSpace.canonicalQueryReadCommand := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

/-- Both physical transfers avoid the two persistent collector words. -/
theorem move_avoids :
    AvoidsCmd (fun i : Fin 330 => i.val = 320 ∨ i.val = 322)
      LeafProgram.QueryReadback.moveCommand := by
  exact ⟨avoids_transferProgram _ 261 324 0 1 (by decide) (by decide),
    avoids_transferProgram _ 324 323 0 1 (by decide) (by decide)⟩

theorem query_program_avoids :
    AvoidsProgram (fun i : Fin 330 => i.val = 320 ∨ i.val = 322)
      ReconstructionSpace.canonicalQueryProgram :=
  avoids_compiled _ ReconstructionSpace.canonicalQueryCommand
    ⟨reader_avoids, move_avoids⟩ 261 323

theorem wide_read_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      ReconstructionNative.canonicalWideRead := by
  apply avoids_liftProgram
  exact query_program_avoids

/-- The CRT's entire320-stack bank lies below the collector frame. -/
theorem crt_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      LeafProgram.Count.reconstruct := by
  apply avoids_call_lift_of_range
  intro i
  change ¬(i.val = 320 ∨ i.val = 322)
  omega

theorem cleanup_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      LeafProgram.Count.clearCaches := by
  exact ⟨avoids_clearProgram _ 5 0 1 (by decide),
    avoids_clearProgram _ 10 0 1 (by decide)⟩

theorem command_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      ReconstructionNative.command :=
  ⟨crt_avoids, wide_read_avoids, cleanup_avoids⟩

theorem program_avoids :
    AvoidsProgram (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      ReconstructionNative.program :=
  avoids_compiled _ ReconstructionNative.command command_avoids 256 323

/-- Every actual identity-on-indices embedding, including768 into896, keeps
this no-read/no-write certificate. No execution service is assumed. -/
theorem lifted_avoids {R S : ℕ} (register : Fin 40 → Fin R)
    (stack : Fin 768 → Fin S) (hstack : ∀ i, (stack i).val = i.val) :
    AvoidsCmd (fun i : Fin S => i.val = 320 ∨ i.val = 322)
      (.call (ProgramLinking.liftProgram ReconstructionNative.program register stack)) := by
  apply avoids_liftProgram
  have hp : ((fun i : Fin S => i.val = 320 ∨ i.val = 322) ∘ stack) =
      (fun i : Fin 768 => i.val = 320 ∨ i.val = 322) := by
    funext i
    simp only [Function.comp_apply, hstack]
  rw [hp]
  exact program_avoids

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionReplay
