import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramControl
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramLoops

namespace OAI.Algorithms

/-! Framed invocation of the fixed lower-256 arithmetic controllers. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram

/-- The lower register bank is identical; compilation adds one paid return. -/
abbrev lowerCall (code : Cmd 16 256) (input output : Fin 256) : Code :=
  liftCommand code input output id localPorts

theorem lowerCall_run (code : Cmd 16 256) (input output : Fin 256)
    (d : Data) (after : Fin 256 → List Bool) (K : ℕ)
    (h : SubexpConvolutionControl.ExecutesIn code K (d.stacks ∘ localPorts) after) :
    ∃ n ≤ K + 1, ∃ rf, Eval (lowerCall code input output) n d
      ⟨rf, Function.extend localPorts after d.stacks⟩ := by
  obtain ⟨n, rf, hn, ht⟩ := h d.regs
  have he := eval_liftCommand_from_state code input output id localPorts d
    Function.injective_id localPorts.injective ht
  exact ⟨n + 1, by omega, Function.extend id rf d.regs, he⟩

theorem lower_extend_project (d : Data) :
    Function.extend localPorts (d.stacks ∘ localPorts) d.stacks = d.stacks :=
  congrArg StructuredProgram.State.stacks
    (embedState_project id localPorts d Function.injective_id localPorts.injective)

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
