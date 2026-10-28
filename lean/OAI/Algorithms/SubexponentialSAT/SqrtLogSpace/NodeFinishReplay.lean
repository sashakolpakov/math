import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayFootprint

/-! Concrete no-read/no-write certificates for the emitted-node tail.
These check the actual finite port maps and calls, including every peek;
the pending caller and accumulated count on320/322 are never inspected. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeFinishReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

theorem clearMany_avoids (H : Fin 896 → Prop) (ports : List (Fin 896))
    (hp : ∀ i ∈ ports, ¬ H i) : AvoidsCmd H (NodeReadoutSpace.clearMany ports) := by
  induction ports with
  | nil => exact True.intro
  | cons i ports ih =>
      exact ⟨avoids_clearProgram H i 0 1 (hp i (by simp)),
        ih (fun j hj => hp j (by simp [hj]))⟩

theorem readout_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) NodeReadoutSpace.command := by
  refine ⟨clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      decide
    · have hs := NodeReadoutSpace.scratchPorts_low hi
      omega
  · apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide

theorem prepare_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) NodeAppendSpace.prepare := by
  refine ⟨clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  ·
    exact ⟨avoids_copyProgram _ 194 5 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 202 12 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 204 39 89 0 1 (by decide) (by decide) (by decide)⟩

theorem append_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) NodeAppendSpace.append :=
  ⟨avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 862 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 863 0 1 (by decide) (by decide)⟩

theorem nodeAppend_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) NodeAppendSpace.command :=
  ⟨prepare_avoids, readout_avoids, append_avoids⟩

theorem finishNode_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) QueryNodeFinish.finishNode := by
  refine ⟨clearMany_avoids _ _ ?_, ⟨⟨True.intro, ?_⟩, ?_⟩⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> decide
  · change ¬ ((307 : Fin 896).val = 320 ∨ (307 : Fin 896).val = 322)
    decide
  · change ¬ ((301 : Fin 896).val = 320 ∨ (301 : Fin 896).val = 322)
    decide

theorem command_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) QueryNodeFinish.command :=
  ⟨nodeAppend_avoids, finishNode_avoids⟩

theorem program_avoids :
    AvoidsProgram (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) QueryNodeFinish.program :=
  avoids_compiled _ _ command_avoids 850 863

/-- The full streamed jet handoff used by recovery avoids the same caller words. -/
theorem handoff_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) NodeAppendSpace.handoff :=
  ⟨avoids_clearProgram _ 265 0 1 (by decide),
    avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 265 0 1 (by decide) (by decide)⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeFinishReplay
