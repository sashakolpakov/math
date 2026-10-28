import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionLeafMain
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionLeafCost

namespace OAI.Algorithms

/-! The measured wide-leaf wrapper in the actual Main allocation.  Only the
supplied core trace is assumed; all copying, cleanup and return steps are paid. -/
namespace SubexponentialSAT.SqrtLog.Execution.LeafMain

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupStorage
open SubexpSetupProgram (Config helperSize mainExtraStacks)

theorem prepared_registers (a : LeafIO.Data) (ha : ∀ i, a.regs i = false)
    (i : Fin 40) : (LeafIO.prepared a).regs i = false := by
  have hr : a.regs = fun _ => false := funext ha
  simp [readRegs,hr]

theorem install_finished_registers (c : Config) (hc : 896 < helperSize c)
    (core : Cmd 40 896) (a : MainState finalExtraRegisters (mainExtraStacks c))
    (middle : LeafIO.Data) (i : Fin 40) :
    ((procedure c hc core).install a (LeafIO.finished middle)).regs
      (workRegister finalExtraRegisters i) = false := by
  exact (embedState_register (procedure c hc core).registerMap (stack c hc) a
    (LeafIO.finished middle) (procedure c hc core).registerMap_injective i).trans
      (LeafIO.finished_regs middle i)

/-- This is an actual Main invocation, with a linear overhead in the incoming
word bound and core transition count.  The exact installed state permits reuse
of every literal frame theorem in ExecutionLeafMain. -/
theorem procedure_bounded_eval (c : Config) (hc : 896 < helperSize c)
    (core : Cmd 40 896) (a : MainState finalExtraRegisters (mainExtraStacks c))
    (B : ℕ) (hword : WordBound B ((procedure c hc core).project a))
    (ha : Ready c hc core a) {t : ℕ} {b : State 40 896}
    (hb : Eval core t
      (projectState id LeafIO.work (LeafIO.prepared ((procedure c hc core).project a))) b) :
    ∃ total out, Eval (procedure c hc core).invoke total a out ∧
      total ≤ 100001*(B+t+1) ∧
      out = (procedure c hc core).install a
        (LeafIO.finished (embedState id LeafIO.work
          (LeafIO.prepared ((procedure c hc core).project a)) b)) ∧
      out.stacks (persistent (mainExtraStacks c) 10) = b.stacks 787 ∧
      (∀ i : Fin 896, out.stacks (WideLeaf.stack c hc i) = []) ∧
      (∀ i : Fin 40, out.regs (workRegister finalExtraRegisters i) = false) ∧
      (∀ i : Fin 3, out.regs (controlRegister finalExtraRegisters i) =
        a.regs (controlRegister finalExtraRegisters i)) := by
  obtain ⟨steps,result,he,hle,rfl⟩ :=
    LeafIO.command_bounded_eval core ((procedure c hc core).project a) B hword ha hb
  refine ⟨steps+1,_,procedureOfCommand_eval (LeafIO.command core) 896 899
    WideLeaf.register ⟨stack c hc,stack_injective c hc⟩ a he,?_,rfl,?_,?_,?_,?_⟩
  · omega
  · exact install_finished_answer c hc core a ha b
  · intro i
    exact install_finished_work c hc core a _ i
  · intro i
    exact install_finished_registers c hc core a _ i
  · intro i
    exact Procedure.install_control (procedure c hc core) a _ i

end SubexponentialSAT.SqrtLog.Execution.LeafMain

end OAI.Algorithms
