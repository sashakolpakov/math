import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCarried
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQuerySetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramInterpolationReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQueryReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeOuter

namespace OAI.Algorithms

/-! Actual per-query evaluation is independent of the arbitrary outer collector
source and accumulator. This gives exact-time replay, including all setup and
cleanup, without hiding the live reference, branch counter, or branch mass. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Carried
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay

theorem arithmetic_avoids : AvoidsCmd hidden arithmetic :=
  ⟨⟨avoidsCmd_mono subset LeafRingSetupProgram.Replay.producerWideCall_avoids,
    avoidsCmd_mono subset LeafRingSetupProgram.Interpolation.Replay.command_avoids⟩,
    avoidsCmd_mono subset LayoutDenominatorProgramQuery.command_avoids⟩

theorem prepare_avoids : AvoidsCmd hidden prepare := by
  refine ⟨⟨?_,?_⟩,countPrepare_avoids⟩
  · exact avoids_clearProgram hidden 190 0 1 (by decide)
  · exact avoids_clearProgram hidden 191 0 1 (by decide)

theorem residual_avoids : AvoidsCmd hidden Residual.command := by
  apply avoidsCmd_mono (K:=Residual.Native.outerTape) _ Residual.Native.outer_command_avoids
  intro i hi
  simpa only [Residual.Native.outerTape,OuterCarried.hidden,List.mem_cons,List.not_mem_nil,or_false] using subset i hi

theorem success_avoids : AvoidsCmd hidden success :=
  ⟨avoidsCmd_mono subset PackingCallerProgram.Replay.command_avoids,
    arithmetic_avoids,prepare_avoids,branches_avoids _ residual_avoids⟩

theorem command_avoids (k : ℕ) : AvoidsCmd hidden (command k) :=
  ⟨avoidsCmd_mono subset (LeafQueryFrontend.frontend_avoids_outerCarried k),
    success_avoids,cleanup_avoids⟩

theorem marked_avoids (k : ℕ) : AvoidsCmd hidden (marked k) :=
  ⟨markInput_avoids,command_avoids k⟩

theorem accepted_avoids (k : ℕ) : AvoidsCmd hidden (accepted k) :=
  ⟨noMarkInput_avoids,command_avoids k⟩

def reference (a : Data) : Data := rebaseState hidden (fun _ => []) a
def restore (a b : Data) : Data := rebaseState hidden a.stacks b

theorem reference_visible (a : Data) (i : Fin 768) (hi : ¬hidden i) :
    (reference a).stacks i=a.stacks i := by
  simp [reference,rebaseState,rebaseStacks,hi]

theorem reference_width (a : Data) (W : ℕ)
    (hw : ∀i,¬hidden i → (a.stacks i).length ≤ W) :
    ∀i,((reference a).stacks i).length ≤ W := by
  intro i
  by_cases hi : hidden i
  · simp [reference,rebaseState,rebaseStacks,hi]
  · rw [reference_visible a i hi]
    exact hw i hi

theorem restore_reference (a : Data) : restore a (reference a)=a := by
  apply congrArg (StructuredProgram.State.mk a.regs)
  funext i
  by_cases hi : hidden i <;> simp [reference,rebaseState,rebaseStacks,hi]

theorem marked_replay (k : ℕ) {n : ℕ} (a b : Data)
    (he : Eval (marked k) n (reference a) b) :
    Eval (marked k) n a (restore a b) := by
  have h := eval_rebase hidden (marked_avoids k) he a.stacks
  change Eval (marked k) n (restore a (reference a)) (restore a b) at h
  simpa only [restore_reference] using h

theorem accepted_replay (k : ℕ) {n : ℕ} (a b : Data)
    (he : Eval (accepted k) n (reference a) b) :
    Eval (accepted k) n a (restore a b) := by
  have h := eval_rebase hidden (accepted_avoids k) he a.stacks
  change Eval (accepted k) n (restore a (reference a)) (restore a b) at h
  simpa only [restore_reference] using h

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Carried

end OAI.Algorithms
