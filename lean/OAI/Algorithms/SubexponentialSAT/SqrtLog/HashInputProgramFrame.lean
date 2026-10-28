import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramFrame
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Paid construction of the agreed inline record payload: a framed flat ring
coefficient followed by the ORIGINAL canonical literal-list payload. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Frame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

def data (regs : Fin 3 → Bool) (weight clause tmp : List Bool) : State 3 3 :=
  ⟨regs,![weight,clause,tmp]⟩

abbrev reverseWeight : Cmd 3 3 := .call (StackRoutines.transferProgram 0 2 0 1)
def emitPorts : Fin 2 → Fin 3 := ![2,1]
theorem emitPorts_injective : Function.Injective emitPorts := by decide
abbrev emit : Cmd 3 3 := .call (ProgramLinking.liftProgram
  Squarefree.Program.frameEmitProgram id emitPorts)
abbrev command : Cmd 3 3 := .seq reverseWeight emit

theorem reverseWeight_eval (regs : Fin 3 → Bool) (weight clause : List Bool) :
    Eval reverseWeight (3*weight.length+3) (data regs weight clause [])
      (data (readRegs regs 0 1 none) [] clause weight.reverse) := by
  have h := transfer_eval (data regs weight clause []) 0 2 0 1 (by decide) (by decide)
  convert h using 1
  · simp [data]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [data, StackRoutines.transferStacks]

theorem emit_eval (regs : Fin 3 → Bool) (weight clause : List Bool) :
    ∃ rr, Eval emit (4*weight.length+6)
      (data regs [] clause weight.reverse)
      (data rr [] (Encoding.frame weight ++ clause) []) := by
  obtain ⟨rr,ht⟩ := Squarefree.Program.frameEmit_trace weight clause regs
  have hi : embedState id emitPorts (data regs [] clause weight.reverse)
      (Squarefree.Program.frameData regs weight.reverse clause) =
      data regs [] clause weight.reverse := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id emitPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have ho : embedState id emitPorts (data regs [] clause weight.reverse)
      (Squarefree.Program.frameData rr [] (Encoding.frame weight ++ clause)) =
      data rr [] (Encoding.frame weight ++ clause) [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id emitPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [data,emitPorts,Fin.exists_fin_succ]
  have he := eval_call_lifted Squarefree.Program.frameEmitProgram id emitPorts
    (data regs [] clause weight.reverse) Function.injective_id emitPorts_injective ht
  rw [hi,ho] at he
  exact ⟨rr,he⟩

theorem command_eval (regs : Fin 3 → Bool) (weight clause : List Bool) :
    ∃ rr, Eval command (7*weight.length+9)
      (data regs weight clause [])
      (data rr [] (Encoding.frame weight ++ clause) []) := by
  obtain ⟨rr,he⟩ := emit_eval (readRegs regs 0 1 none) weight clause
  refine ⟨rr,?_⟩
  have hh := (reverseWeight_eval regs weight clause).seq he
  convert hh using 1 ; first | rfl | omega

def program := compiled command 0 1

theorem program_runs (regs : Fin 3 → Bool) (weight clause : List Bool) :
    ∃ rr, RunsIn program (7*weight.length+10)
      ((data regs weight clause []).withPC (some program.entry))
      ((data rr [] (Encoding.frame weight ++ clause) []).withPC none) := by
  obtain ⟨rr,he⟩ := command_eval regs weight clause
  exact ⟨rr,⟨7*weight.length+9+1,by omega,compiled_halt_trace he 0 1⟩⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.Frame

end OAI.Algorithms
