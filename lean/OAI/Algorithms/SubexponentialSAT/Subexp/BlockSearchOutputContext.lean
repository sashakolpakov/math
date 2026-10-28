import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchExecution

namespace OAI.Algorithms

/-! Persistent arithmetic data retained by the actual basis-search program. -/

namespace SubexponentialSAT.Subexp.BlockSearchOutputContext

open BitProgram StructuredCalls BlockSearchProgram BlockSearchLoop BlockSearchNested
open BlockSearchOuter BlockSearchEncoding BlockSearchPredicate SubexpTupleRefinement

def Retained (ctx : Context) (a : StructuredProgram.State 24 42) : Prop :=
  a.stacks 27 = ctx.modulus ∧ a.stacks 36 = ctx.zeroWord ∧
  a.stacks 38 = ctx.matrix ∧ a.stacks 39 = ctx.rowCount ∧ a.stacks 10 = ctx.dimension

theorem command_retains (matrixPair : Cmd 24 42) (ctx : Context)
    (coefficients dimensions tables : List (List Bool)) (limit tableLimit : ℕ)
    (test : List Bool → List Bool → List Bool → Bool)
    (cost : List Bool → List Bool → List Bool → ℕ)
    (validTable validSplit validCoefficient : List Bool → Prop)
    (htableLimit : ∀ bits, validTable bits → bits.length ≤ tableLimit)
    (hreversal : ∀ bits, validSplit bits → bits.reverse = bits)
    (hlimit : ∀ bits, validSplit bits → bits.length ≤ limit)
    (hcoefficients : ∀ bits ∈ coefficients, validCoefficient bits)
    (hdimensions : ∀ bits ∈ dimensions, validSplit bits)
    (htables : ∀ bits ∈ tables, validTable bits)
    (contract : ∀ table, validTable table → ∀ split, validSplit split →
      CoefficientContract matrixPair ctx table split (test table split) (cost table split)
        validCoefficient)
    (base : StructuredProgram.State 24 42)
    (hb : TableEntry ctx coefficients dimensions limit tableLimit base)
    (h0 : base.stacks 0 = ProgramEncoding.encodeRecords tables) (h2 : base.stacks 2 = []) :
    ∃ n next, Retained ctx next ∧ Eval (BlockSearchLoop.command matrixPair) n base next := by
  have hc := tableContract matrixPair ctx coefficients dimensions limit tableLimit test cost
    validTable validSplit validCoefficient htableLimit hreversal hlimit hcoefficients
    hdimensions contract
  obtain ⟨n, b, hn, hi, history, heval⟩ := RecordPrograms.iterate_run_with_on tablePorts
    (tableCallback matrixPair) (tableTest coefficients dimensions test)
    (fun table => tableCost tableLimit limit (cost table) coefficients dimensions table)
    (TableEntry ctx coefficients dimensions limit tableLimit)
    (fun table _ b => Selected coefficients dimensions test table b) validTable hc tables []
    base htables hb (base.regs 8) (base.regs 9) (base.regs 10)
  let middle := RecordPrograms.state tablePorts b false true
    (tables.any (tableTest coefficients dimensions test))
    (RecordPrograms.unread (tableTest coefficients dimensions test) tables []) []
  let next := clearState middle 0
  have hstart : RecordPrograms.state tablePorts base (base.regs 8) (base.regs 9)
      (base.regs 10) (ProgramEncoding.encodeRecords tables ++ []) [] = base := by
    apply RecordPrograms.state_eq_self <;> simp [tablePorts, h0, h2]
  have hrun : Eval (anyCommand tablePorts (tableCallback matrixPair)) n base middle := by
    rw [← hstart]
    simpa only [middle] using heval
  have ht := hrun.seq (clear_eval middle 0)
  refine ⟨_, next, ?_, ht⟩
  rcases hi.1.1 with ⟨hm, hz, hM, hr, hd, _⟩
  change Retained ctx (clearState middle 0)
  simpa [Retained, next, middle, clearState, StackRoutines.clearStacks,
    RecordPrograms.state, tablePorts] using And.intro hm (And.intro hz (And.intro hM ⟨hr, hd⟩))

/-- A companion to `BlockSearchExecution.program_runsIn`: it identifies
the retained context of any actual completed run, without changing its
instruction bound or the successful-candidate API. -/
theorem program_retains {K : Type*} [Field K] [DecidableEq K]
    (matrixPair : Cmd 24 42) (ctx : Context)
    (code : StackEncoding.BlockCode K) (alphabet : List K)
    {m N : ℕ} (M : Fin m → Fin N → K) (bound : ℕ)
    (hdimension : ctx.dimension = List.replicate N true)
    (contract : ∀ (C : Fin N → Fin N → K) (d : Fin (N + 1)),
      CoefficientContract matrixPair ctx (encodeTuple code (flattenTable C)) (splitCode d)
        (encodedTest code alphabet M (encodeTuple code (flattenTable C)) (splitCode d))
        (fun _ => bound) (BlockSearchCoverage.ValidCoefficient code N))
    (regs : Fin 24 → Bool) {budget : ℕ} {result : StructuredProgram.State 24 42}
    (run : RunsIn (BlockSearchExecution.program matrixPair) budget
      ((BlockSearchExecution.inputState ctx code alphabet N regs).withPC
        (some (BlockSearchExecution.program matrixPair).entry)) (result.withPC none)) :
    Retained ctx result := by
  obtain ⟨np, prepared, hnp, hp, h0, h2, hep⟩ := BlockSearchSetup.command_eval ctx
    (alphabet.map code.block) (List.replicate (N * N) true) (List.replicate N true)
    regs (N * N * code.width) (by simpa using hdimension)
  simp only [List.length_replicate] at hp h0
  have hc : ∀ table, BlockSearchCoverage.ValidTable code N table →
      ∀ split, BlockSearchCoverage.ValidSplit N split →
      CoefficientContract matrixPair ctx table split (encodedTest code alphabet M table split)
        (fun _ => bound) (BlockSearchCoverage.ValidCoefficient code N) := by
    rintro table ⟨C, rfl⟩ split ⟨d, rfl⟩
    exact contract C d
  obtain ⟨ns, next, hnext, he⟩ := command_retains matrixPair ctx
    (BlockSearchCoverage.coefficients code alphabet N) (BlockSearchCoverage.dimensions N)
    (BlockSearchCoverage.tables code alphabet N) N (N * N * code.width)
    (encodedTest code alphabet M) (fun _ _ _ => bound)
    (BlockSearchCoverage.ValidTable code N) (BlockSearchCoverage.ValidSplit N)
    (BlockSearchCoverage.ValidCoefficient code N)
    (fun bits h => (BlockSearchCoverage.valid_table_length code N bits h).le)
    (BlockSearchCoverage.valid_split_reverse N) (BlockSearchCoverage.valid_split_length N)
    (BlockSearchCoverage.valid_coefficient code alphabet N) (BlockSearchCoverage.valid_split N)
    (BlockSearchCoverage.valid_table code alphabet N) hc prepared hp h0 h2
  have full := compiled_halt_trace
    (hep.seq (Eval.call (BlockSearchLoop.program matrixPair)
      (compiled_halt_trace he 0 41))) 0 41
  have run' : RunsIn (BlockSearchExecution.program matrixPair) (np + (ns + 1) + 1)
      ((BlockSearchExecution.inputState ctx code alphabet N regs).withPC
        (some (BlockSearchExecution.program matrixPair).entry)) (next.withPC none) :=
    ⟨_, le_rfl, full⟩
  have hsame := Computation.RunsIn.terminal_unique run run' rfl rfl
  have hd : result = next := by
    simpa only [StructuredProgram.State.ofCfg_withPC] using
      congrArg StructuredProgram.State.ofCfg hsame
  rw [hd]
  exact hnext

end SubexponentialSAT.Subexp.BlockSearchOutputContext

end OAI.Algorithms
