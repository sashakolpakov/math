import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramBinary
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev ArithData := State 8 14
def countRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def countStacks : Fin 3 → Fin 14 := ![13,3,12]
theorem countRegisters_injective : Function.Injective countRegisters := Fin.castAdd_injective _ _
theorem countStacks_injective : Function.Injective countStacks := by decide

/-- Preserve the unary count word on2 and compute its binary length on3. -/
abbrev count : Cmd 8 14 := .seq (ArithmeticCalls.copyAt 2 13 12)
  (liftCommand LeafStatisticsProgram.Binary.command 0 1 countRegisters countStacks)

theorem count_eval (d : ArithData) (h3 : d.stacks 3 = [])
    (h12 : d.stacks 12 = []) (h13 : d.stacks 13 = []) :
    ∃ t ≤ (d.stacks 2).length * (8 * (d.stacks 2).length + 10) +
      7 * (d.stacks 2).length + 10, ∃ rf word,
      Eval count t d ⟨rf, Function.update d.stacks 3 word⟩ ∧
      BinaryArithmetic.toNat word = (d.stacks 2).length ∧
      word.length ≤ (d.stacks 2).length := by
  let a := ArithmeticCalls.afterCopy 2 13 d
  have ha := ArithmeticCalls.copyAt_eval 2 13 12 d
    (by decide) (by decide) (by decide) h13 h12
  obtain ⟨n, word, hn, hv, hl, he⟩ := LeafStatisticsProgram.Binary.command_eval
    (fun i => a.regs (countRegisters i)) (d.stacks 2)
  have hp : projectState countRegisters countStacks a =
      LeafStatisticsProgram.Binary.state (fun i => a.regs (countRegisters i)) (d.stacks 2) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [ countStacks, a, ArithmeticCalls.afterCopy, CounterPrograms.lengthStacks, h3, h12]
  rw [← hp] at he
  let b := LeafStatisticsProgram.Binary.state (fun _ => false) [] word
  let e := embedState countRegisters countStacks a b
  have hb : e = (⟨e.regs, Function.update d.stacks 3 word⟩ : ArithData) := by
    apply embedState_eq_of_ports countRegisters countStacks a _ b
      countRegisters_injective countStacks_injective
    · intro i; exact embedState_register countRegisters countStacks a b countRegisters_injective i
    · intro i hi; exact embedState_register_frame countRegisters countStacks a b i hi
    · intro i; fin_cases i <;>
        simp [b, countStacks, LeafStatisticsProgram.Binary.state,
          CounterPrograms.lengthStacks, h12, h13]
    · intro i hi
      have hi3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
      have hi13 : i ≠ 13 := fun h => hi ⟨0, h.symm⟩
      simp [a, ArithmeticCalls.afterCopy, hi3, hi13]
  have hrun := eval_liftCommand_from_state LeafStatisticsProgram.Binary.command 0 1
    countRegisters countStacks a countRegisters_injective countStacks_injective he
  change Eval _ (n+1) a e at hrun
  rw [hb] at hrun
  exact ⟨(7 * (d.stacks 2).length + 5) + (n+1), by omega,
    e.regs, word, ha.seq hrun, hv, hl⟩

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
