import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCalls
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBanked

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
open LeafParametersProgram

theorem parameterCall_eval (a : Data) (x : Input) (l : Fin 8 → ℕ) (w : Bank.Words)
    (hs : Circuit.Shape (Layout.initialModel x l) w)
    (hp : projectState r9 bank a = Execute.state (a.regs ∘ r9) w) :
    ∃ n ≤ Execute.runtimeBound x l+1, ∃ rf wf,
      Eval parameterCall n a (embedState r9 bank a (Execute.state rf wf)) ∧
      (rf 8=true ↔ Guard x) ∧ Circuit.Shape (Execute.guardedModel x l) wf ∧
      (Guard x → Layout.EncodesParameters (produce x) wf) := by
  obtain ⟨n,rf,wf,he,hg,hshape,hparams,hn⟩ := Execute.setup_banked_output x l w (a.regs ∘ r9) hs
  have ht := compiled_halt_trace he (Bank.port 0) (Bank.port 42)
  rw [←hp] at ht
  exact ⟨n+1,by omega,rf,wf,
    eval_call_from_state Execute.program r9 bank a (registers_injective ..) (block_injective ..) ht,
    hg,hshape,hparams⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
