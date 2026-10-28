import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SubexpFactorCountSetup
import OAI.Algorithms.SubexponentialSAT.SubexpScopeCountSetup
import OAI.Algorithms.SubexponentialSAT.SubexpClauseMastersProgram

namespace OAI.Algorithms

/-! Small framing lemma for the fixed high-incidence preparation calls. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem lift_update {r s R S : ℕ} (c : Cmd r s) (input output : Fin s)
    (reg : Fin r → Fin R) (stk : Fin s → Fin S) (d : State R S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (j : Fin s) (word : List Bool) (rf : Fin r → Bool) (time : ℕ)
    (he : Eval c time (projectState reg stk d)
      ⟨rf, Function.update (projectState reg stk d).stacks j word⟩) :
    ∃ regs, Eval (liftCommand c input output reg stk) (time + 1) d
      ⟨regs, Function.update d.stacks (stk j) word⟩ := by
  have h := eval_liftCommand_from_state c input output reg stk d hr hs he
  let b := embedState reg stk d
    (⟨rf, Function.update (projectState reg stk d).stacks j word⟩ : State r s)
  have hb : b.stacks = Function.update d.stacks (stk j) word := by
    change Function.extend stk (Function.update _ j word) d.stacks = _
    rw [ProgramLinking.extend_update hs]
    have hp : Function.extend stk (projectState reg stk d).stacks d.stacks = d.stacks :=
      congrArg StructuredProgram.State.stacks (embedState_project reg stk d hr hs)
    rw [hp]
  refine ⟨b.regs, ?_⟩
  change Eval _ _ d b at h
  have hb' : b = (⟨b.regs, Function.update d.stacks (stk j) word⟩ : State R S) :=
    congrArg (fun stkOut => (⟨b.regs, stkOut⟩ : State R S)) hb
  rwa [hb'] at h

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
