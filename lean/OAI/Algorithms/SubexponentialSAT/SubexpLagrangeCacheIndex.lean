import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheControl

namespace OAI.Algorithms

/-! The cache loop compares its actual preserved unary position words. -/

namespace SubexponentialSAT.SubexpLagrangeCacheIndex

open BitProgram StructuredCalls SubexpLagrangeCacheControl

theorem compare_eval (a : Data)
    (h120 : a.stacks 120 = []) (h236 : a.stacks 236 = [])
    (h237 : a.stacks 237 = []) (h238 : a.stacks 238 = []) :
    ∃ n ≤ 18 * (a.stacks 248).length + 9 * (a.stacks 249).length + 34,
      ∃ rf, Eval compareIndices n a ⟨rf, a.stacks⟩ ∧
        rf 7 = decide (a.stacks 248 = a.stacks 249) := by
  let small := projectState compareRegisters comparePorts a
  obtain ⟨rf, ⟨n, hn, ht⟩, hf⟩ := Subexp.ConstraintEntryCompare.program_runsIn small
    (by simpa [small, projectState, comparePorts] using h120)
    (by simpa [small, projectState, comparePorts] using h236)
    (by simpa [small, projectState, comparePorts] using h237)
    (by simpa [small, projectState, comparePorts] using h238)
  have he := eval_call_from_state Subexp.ConstraintEntryCompare.program
    compareRegisters comparePorts a compareRegisters.injective comparePorts_injective ht
  let final := embedState compareRegisters comparePorts a (⟨rf, small.stacks⟩ : Subexp.ConstraintEntryCompare.Data)
  have hs : final.stacks = a.stacks := by
    change Function.extend comparePorts (a.stacks ∘ comparePorts) a.stacks = a.stacks
    exact congrArg StructuredProgram.State.stacks
      (embedState_project compareRegisters comparePorts a compareRegisters.injective comparePorts_injective)
  have hfinal : final = (⟨final.regs, a.stacks⟩ : Data) :=
    congrArg (StructuredProgram.State.mk final.regs) hs
  have hflag : final.regs 7 = decide (a.stacks 248 = a.stacks 249) := by
    change final.regs (compareRegisters 7) = _
    rw [embedState_register _ _ _ _ compareRegisters.injective]
    simpa [small, projectState, comparePorts] using hf
  refine ⟨n, ?_, final.regs, ?_, hflag⟩
  · simpa [small, projectState, comparePorts] using hn
  · change Eval compareIndices n a final at he
    rw [hfinal] at he
    exact he

theorem compare_unary (a : Data) (i j : ℕ)
    (hi : a.stacks 248 = List.replicate i false)
    (hj : a.stacks 249 = List.replicate j false)
    (h120 : a.stacks 120 = []) (h236 : a.stacks 236 = [])
    (h237 : a.stacks 237 = []) (h238 : a.stacks 238 = []) :
    ∃ n ≤ 18 * i + 9 * j + 34, ∃ rf,
      Eval compareIndices n a ⟨rf, a.stacks⟩ ∧ rf 7 = decide (i = j) := by
  obtain ⟨n, hn, rf, he, hf⟩ := compare_eval a h120 h236 h237 h238
  have heq : (List.replicate i false = List.replicate j false) ↔ i = j := by
    constructor
    · intro h
      simpa only [List.length_replicate] using congrArg List.length h
    · rintro rfl; rfl
  refine ⟨n, ?_, rf, he, ?_⟩
  · simpa [hi, hj] using hn
  · simpa only [hi, hj, heq] using hf

end SubexponentialSAT.SubexpLagrangeCacheIndex

end OAI.Algorithms
