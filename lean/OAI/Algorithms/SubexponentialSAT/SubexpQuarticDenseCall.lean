import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticDenseData
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatLift

namespace OAI.Algorithms

/-! Preserving multiplication of the dense caller's two coefficient masters. -/

namespace SubexponentialSAT.SubexpQuarticDenseCall

open BitProgram StackRoutines StructuredCalls
open SubexpLiftRing SubexpQuarticRing SubexpQuarticFlatMul SubexpQuarticFlatLift

abbrev command : Cmd 16 128 := .seq loadCmd (.call denseProgram)

/-- Both coefficient masters and every caller stack except output 13 are preserved. -/
theorem command_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (regs : Fin 16 → Bool) (stk : Stacks (Fin 128))
    (hworkspace : ∀ i, stk (densePorts i) = workspace M.bits width t i)
    (ha : stk 94 = flat a) (hb : stk 96 = flat b) (htmp : stk 24 = []) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool),
      n ≤ 400000 * (baseWidth p μ + 1)^2 + 56 * baseWidth p μ + 10 ∧
      Eval command n ⟨regs, stk⟩
        ⟨resultRegs denseRegisters rf regs,
          Function.update stk 13 (flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1)⟩ := by
  have h11 : stk 11 = [] := hworkspace 70
  have h12 : stk 12 = [] := hworkspace 71
  have hl := load_eval a b regs stk ha hb h11 h12 htmp
  obtain ⟨n, rf, hn, hm⟩ := denseProgram_eval p μ M t a b width hw
    (readRegs regs 0 1 none) (loadedStacks a b stk)
    (loaded_workspace M.bits width t a b stk hworkspace)
  change Eval (.call denseProgram) n _
    ⟨resultRegs denseRegisters rf (readRegs regs 0 1 none),
      resultStacks densePorts (flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1)
        (loadedStacks a b stk)⟩ at hm
  rw [resultRegs_read, result_loaded a b _ stk h11 h12] at hm
  refine ⟨56 * baseWidth p μ + 10 + n, rf, by omega, ?_⟩
  exact hl.seq hm

abbrev program : Program 16 128 (size command + 1) := compiled command 94 13

theorem program_run (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (regs : Fin 16 → Bool) (stk : Stacks (Fin 128))
    (hworkspace : ∀ i, stk (densePorts i) = workspace M.bits width t i)
    (ha : stk 94 = flat a) (hb : stk 96 = flat b) (htmp : stk 24 = []) :
    ∃ rf : Fin 8 → Bool,
      RunsIn program (400000 * (baseWidth p μ + 1)^2 + 56 * baseWidth p μ + 11)
        ⟨some program.entry, regs, stk⟩
        ⟨none, resultRegs denseRegisters rf regs,
          Function.update stk 13 (flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1)⟩ := by
  obtain ⟨n, rf, hn, he⟩ := command_eval p μ M t a b width hw regs stk hworkspace ha hb htmp
  exact ⟨rf, n + 1, by omega, compiled_halt_trace he 94 13⟩

theorem program_primitive (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (regs : Fin 16 → Bool) (stk : Stacks (Fin 128))
    (hworkspace : ∀ i, stk (densePorts i) = workspace M.bits width t i)
    (ha : stk 94 = flat a) (hb : stk 96 = flat b) (htmp : stk 24 = []) :
    ∃ rf : Fin 8 → Bool,
      PrimitiveRunsIn program
        (primitiveOverhead program *
          (400000 * (baseWidth p μ + 1)^2 + 56 * baseWidth p μ + 11))
        ⟨some program.entry, regs, stk⟩
        ⟨none, resultRegs denseRegisters rf regs,
          Function.update stk 13 (flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1)⟩ := by
  obtain ⟨rf, hr⟩ := program_run p μ M t a b width hw regs stk hworkspace ha hb htmp
  exact ⟨rf, primitiveRunsIn_of_runsIn _ hr⟩

end SubexponentialSAT.SubexpQuarticDenseCall

end OAI.Algorithms
