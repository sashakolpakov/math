import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatMul

namespace OAI.Algorithms

/-!
Physical caller-state interfaces for flat quartic multiplication. Relocation
changes only the finite instruction table. The caller's unassigned stacks and
registers are preserved by the actual instruction trace.
-/

namespace SubexponentialSAT.SubexpQuarticFlatLift

open BitProgram StackRoutines StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpQuarticFlatMul


abbrev programAt {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 77 ↪ Fin s) :
    Program r s (size SubexpQuarticFlatMul.command + 1) :=
  ProgramLinking.liftProgram SubexpQuarticFlatMul.program registers ports

/-- A complete run in the caller's physical registers and stack positions. -/
theorem programAt_run {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 77 ↪ Fin s)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hstore : ∀ i, stk (ports i) = initialStore M.bits width t a b i) :
    ∃ rf : Fin 8 → Bool,
      RunsIn (programAt registers ports) (400000 * (baseWidth p μ + 1)^2)
        ⟨some (programAt registers ports).entry, regs, stk⟩
        ⟨none, resultRegs registers rf regs,
          resultStacks ports (flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1) stk⟩ := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpQuarticFlatMul.program_run p μ M t a b width hw
    (fun i => regs (registers i))
  have lifted := ProgramLinking.liftProgram_trace SubexpQuarticFlatMul.program
    registers ports
    (⟨none, regs, stk⟩ : Cfg r s (size SubexpQuarticFlatMul.command + 1))
    registers.injective ports.injective ht
  have hregs := extend_agree registers (fun i => regs (registers i)) regs (fun _ => rfl)
  have hinput := extend_agree ports (initialStore M.bits width t a b) stk hstore
  have houtput := extend_final ports M.bits width t a b
    (SubexpPreparedQuartic.binaryMul p μ M t a b).1 stk hstore
  refine ⟨rf, n, hn, ?_⟩
  simpa only [ProgramLinking.embedCfg, ProgramLinking.relocatePc, id_eq,
    hregs, hinput, houtput, programAt, ProgramLinking.liftProgram, resultRegs] using lifted

theorem programAt_eval {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 77 ↪ Fin s)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hstore : ∀ i, stk (ports i) = initialStore M.bits width t a b i) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ 400000 * (baseWidth p μ + 1)^2 ∧
      Eval (.call (programAt registers ports)) n ⟨regs, stk⟩
        ⟨resultRegs registers rf regs,
          resultStacks ports (flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1) stk⟩ := by
  obtain ⟨rf, n, hn, ht⟩ := programAt_run registers ports p μ M t a b width hw regs stk hstore
  exact ⟨n, rf, hn, .call _ ht⟩

theorem programAt_primitive {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 77 ↪ Fin s)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hstore : ∀ i, stk (ports i) = initialStore M.bits width t a b i) :
    ∃ rf : Fin 8 → Bool,
      PrimitiveRunsIn (programAt registers ports)
        (primitiveOverhead (programAt registers ports) * (400000 * (baseWidth p μ + 1)^2))
        ⟨some (programAt registers ports).entry, regs, stk⟩
        ⟨none, resultRegs registers rf regs,
          resultStacks ports (flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1) stk⟩ := by
  obtain ⟨rf, hr⟩ := programAt_run registers ports p μ M t a b width hw regs stk hstore
  exact ⟨rf, primitiveRunsIn_of_runsIn _ hr⟩


abbrev denseProgram : Program 16 128 (size SubexpQuarticFlatMul.command + 1) :=
  programAt denseRegisters densePorts

theorem denseProgram_run (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (regs : Fin 16 → Bool) (stk : Stacks (Fin 128))
    (hstore : ∀ i, stk (densePorts i) = initialStore M.bits width t a b i) :
    ∃ rf : Fin 8 → Bool,
      RunsIn denseProgram (400000 * (baseWidth p μ + 1)^2)
        ⟨some denseProgram.entry, regs, stk⟩
        ⟨none, resultRegs denseRegisters rf regs,
          Function.update (Function.update (Function.update stk 11 []) 12 [])
            13 (flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1)⟩ := by
  exact programAt_run denseRegisters densePorts p μ M t a b width hw regs stk hstore

theorem denseProgram_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (regs : Fin 16 → Bool) (stk : Stacks (Fin 128))
    (hstore : ∀ i, stk (densePorts i) = initialStore M.bits width t a b i) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ 400000 * (baseWidth p μ + 1)^2 ∧
      Eval (.call denseProgram) n ⟨regs, stk⟩
        ⟨resultRegs denseRegisters rf regs,
          Function.update (Function.update (Function.update stk 11 []) 12 [])
            13 (flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1)⟩ := by
  exact programAt_eval denseRegisters densePorts p μ M t a b width hw regs stk hstore

end SubexponentialSAT.SubexpQuarticFlatLift

end OAI.Algorithms
