import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowExecution

namespace OAI.Algorithms

/-! A framed call to the actual row source emitter inside the row workspace. -/

namespace SubexponentialSAT.Subexp.UniversalRowEmitCall

open BitProgram StructuredCalls
open UniversalRowProgram (Row)
open SubexpKernelControl (Word)

abbrev Data := State 8 32

def regs : Fin 3 → Fin 8 := Fin.castAdd 5
def stackMap : Fin 8 → Fin 32 := ![31, 3, 10, 1, 2, 4, 5, 6]
theorem regs_injective : Function.Injective regs := Fin.castAdd_injective 3 5
theorem stackMap_injective : Function.Injective stackMap := by decide

abbrev reset : Cmd 8 32 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 false))) (.base (.atom (.set 2 false))))

def resetState (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 false) 2 false, a.stacks⟩

theorem reset_eval (a : Data) : Eval reset 3 a (resetState a) := by
  exact .seq (.base (.atom _ _)) (.seq (.base (.atom _ _)) (.base (.atom _ _)))

abbrev emit : Cmd 8 32 :=
  .call (ProgramLinking.liftProgram UniversalRowProgram.program regs stackMap)

abbrev command : Cmd 8 32 := .seq reset emit

def result (a : Data) (output : Word) : Data :=
  ⟨(resetState a).regs, Function.update a.stacks 31 output⟩

theorem command_eval (a : Data) (zero one : Word) (r : Row Word)
    (hrow : a.stacks 31 = UniversalRowProgram.encodeRow r)
    (hzero : a.stacks 3 = zero) (hone : a.stacks 10 = one)
    (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = []) (h4 : a.stacks 4 = [])
    (h5 : a.stacks 5 = []) (h6 : a.stacks 6 = []) :
    ∃ n ≤ 2048 * UniversalRowProgram.inputSize zero one r ^ 2 + 3,
      Eval command n a (result a (UniversalRowProgram.rowCode zero one (zero ++ one) r)) := by
  let prepared := resetState a
  let first := SubexpKernelControl.serviceState (UniversalRowProgram.encodeRow r) zero one
  let last := SubexpKernelControl.serviceState (UniversalRowProgram.rowCode zero one (zero ++ one) r)
    zero one
  have hin : embedState regs stackMap prepared first = prepared := by
    apply embedState_eq_of_ports _ _ _ _ _ regs_injective stackMap_injective
    · intro j
      fin_cases j <;> simp [regs, prepared, resetState, first, SubexpKernelControl.serviceState]
    · intros; rfl
    · intro j
      fin_cases j <;> simp [stackMap, prepared, resetState, first,
        SubexpKernelControl.serviceState, SubexpKernelControl.state,
        SubexpKernelControl.emptyAccumulator, hrow, hzero, hone, h1, h2, h4, h5, h6]
    · intros; rfl
  have hout : embedState regs stackMap prepared last =
      result a (UniversalRowProgram.rowCode zero one (zero ++ one) r) := by
    apply embedState_eq_of_ports _ _ _ _ _ regs_injective stackMap_injective
    · intro j
      fin_cases j <;> simp [regs, result, resetState, last, SubexpKernelControl.serviceState]
    · intro j hj
      rfl
    · intro j
      fin_cases j <;> simp [stackMap, result, last, SubexpKernelControl.serviceState,
        SubexpKernelControl.state, SubexpKernelControl.emptyAccumulator,
        hzero, hone, h1, h2, h4, h5, h6]
    · intro j hj
      have h31 : j ≠ 31 := fun h => hj ⟨0, h.symm⟩
      simp [result, prepared, resetState, h31]
  obtain ⟨n, hn, ht⟩ := UniversalRowProgram.program_runsIn zero one r
  have he := eval_call_lifted UniversalRowProgram.program regs stackMap prepared
    regs_injective stackMap_injective (a := first) (b := last) ht
  have hem : Eval emit n prepared
      (result a (UniversalRowProgram.rowCode zero one (zero ++ one) r)) := by
    simpa only [emit, hin, hout] using he
  exact ⟨3 + n, by omega, (reset_eval a).seq hem⟩

abbrev program : Program 8 32 (size command + 1) := compiled command 31 31

theorem program_runsIn (a : Data) (zero one : Word) (r : Row Word)
    (hrow : a.stacks 31 = UniversalRowProgram.encodeRow r)
    (hzero : a.stacks 3 = zero) (hone : a.stacks 10 = one)
    (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = []) (h4 : a.stacks 4 = [])
    (h5 : a.stacks 5 = []) (h6 : a.stacks 6 = []) :
    RunsIn program (2048 * UniversalRowProgram.inputSize zero one r ^ 2 + 4)
      (a.withPC (some program.entry))
      ((result a (UniversalRowProgram.rowCode zero one (zero ++ one) r)).withPC none) := by
  obtain ⟨n, hn, he⟩ := command_eval a zero one r hrow hzero hone h1 h2 h4 h5 h6
  exact ⟨n + 1, by omega, compiled_halt_trace he 31 31⟩

end SubexponentialSAT.Subexp.UniversalRowEmitCall

end OAI.Algorithms
