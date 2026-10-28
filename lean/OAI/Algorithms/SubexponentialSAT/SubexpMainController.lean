import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainRuntime

namespace OAI.Algorithms

/-!
# Main controller with a fixed guarded leaf program

The leaf callback is actual finite command code. This variant permits the
physical empty-clause guard to skip layout and reconstruction, while reusing
the existing setup, sparsifier, record parser, and finite-input fallback.
Every execution hypothesis below is a trace of that fixed code.
-/

namespace SubexponentialSAT.SubexpMainController

open StructuredCalls SubexpMainProgram

variable {er es : ℕ}

def command (p : Phases er es) (leaf : MainCmd er es) : MainCmd er es :=
  .seq (frontendProcedure er es).invoke (.seq p.setup.invoke (.seq p.sparsify.invoke
    (.seq (RecordPrograms.iterate (ports er es) leaf) (emitAnswer er es))))

def program (p : Phases er es) (leaf : MainCmd er es) :=
  StructuredCalls.compiled (command p leaf) (persistent es 0) (persistent es 11)

theorem command_execution {p : Phases er es} {leaf : MainCmd er es} {input : List Bool}
    {afterPrefix : MainState er es} {prefixSteps : ℕ}
    (prefixTrace : Eval (frontendProcedure er es).invoke prefixSteps
      (initialData er es input) afterPrefix)
    (boot : BootRun p afterPrefix)
    (records : List (List Bool)) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : MainState er es → Prop) (validPayload : List Bool → Prop)
    (contract : RecordPrograms.CallbackContractOn (ports er es) leaf
      test cost invariant validPayload)
    (validRecords : ∀ bits ∈ records, validPayload bits)
    (valid : invariant boot.afterSparsify)
    (source : boot.afterSparsify.stacks (persistent es 7) = Encoding.encodeList id records)
    (payload : boot.afterSparsify.stacks (persistent es 8) = []) :
    ∃ (n : ℕ) (final : MainState er es),
      n ≤ prefixSteps + boot.setupSteps + boot.sparsifySteps +
        4 + RecordPrograms.budget cost records ∧
      Eval (command p leaf) n (initialData er es input) final ∧
      (final.stacks (persistent es 11)).head? = some (records.any test) := by
  let a := boot.afterSparsify
  have ha : RecordPrograms.state (ports er es) a
      (a.regs (controlRegister er 0)) (a.regs (controlRegister er 1))
      (a.regs (controlRegister er 2)) (Encoding.encodeList id records ++ []) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, ports] using source
    · exact payload
  obtain ⟨n, next, hn, _, hi⟩ := RecordPrograms.iterate_run_on
    (ports er es) leaf test cost invariant validPayload contract records [] a
    validRecords valid (a.regs (controlRegister er 0))
    (a.regs (controlRegister er 1)) (a.regs (controlRegister er 2))
  rw [ha] at hi
  let last := RecordPrograms.state (ports er es) next false true (records.any test)
    (RecordPrograms.unread test records []) []
  refine ⟨prefixSteps + (boot.setupSteps + (boot.sparsifySteps + (n + 1))),
    emittedData last, by omega, ?_, ?_⟩
  · exact .seq prefixTrace (.seq boot.setupTrace (.seq boot.sparsifyTrace
      (.seq hi (emitAnswer_eval last))))
  · rw [emitted_head]
    exact congrArg some (RecordPrograms.state_found (ports er es) next false true
      (records.any test) (RecordPrograms.unread test records []) [])

theorem compiled_execution {p : Phases er es} {leaf : MainCmd er es}
    {input : List Bool} {n : ℕ} {final : MainState er es}
    (h : Eval (command p leaf) n (initialData er es input) final) :
    BitProgram.Trace (program p leaf) (n + 1) (BitProgram.initial (program p leaf) input)
      (final.withPC none) :=
  StructuredCalls.compiled_halt_trace h (persistent es 0) (persistent es 11)

/-- The semantic test describes the answer proved for the fixed callback;
the program obtains it from the callback's actual output bit. -/
structure Execution (p : Phases er es) (leaf : MainCmd er es)
    {n : ℕ} (F : SAT.CNF (Fin n)) where
  afterPrefix : MainState er es
  prefixSteps : ℕ
  prefixTrace : Eval (frontendProcedure er es).invoke prefixSteps
    (initialData er es (Encoding.encodeCNF F)) afterPrefix
  boot : BootRun p afterPrefix
  records : List (List Bool)
  test : List Bool → Bool
  cost : List Bool → ℕ
  invariant : MainState er es → Prop
  validPayload : List Bool → Prop
  callback : RecordPrograms.CallbackContractOn (ports er es) leaf
    test cost invariant validPayload
  validRecords : ∀ bits ∈ records, validPayload bits
  valid : invariant boot.afterSparsify
  source : boot.afterSparsify.stacks (persistent es 7) = Encoding.encodeList id records
  payload : boot.afterSparsify.stacks (persistent es 8) = []
  correct : records.any test = true ↔ SAT.Satisfiable F

namespace Execution

variable {p : Phases er es} {leaf : MainCmd er es} {n : ℕ} {F : SAT.CNF (Fin n)}

def bound (run : Execution p leaf F) : ℕ :=
  run.prefixSteps + run.boot.setupSteps + run.boot.sparsifySteps +
    5 + RecordPrograms.budget run.cost run.records

theorem runs (run : Execution p leaf F) :
    ∃ (time : ℕ) (final : BitProgram.Cfg (totalRegs er) (totalStacks es)
        (StructuredCalls.size (command p leaf) + 1)),
      BitProgram.RunsIn (program p leaf) time
        (BitProgram.initial (program p leaf) (Encoding.encodeCNF F)) final ∧
      final.pc = none ∧
      (final.stacks (program p leaf).outputStack).head? = some (run.records.any run.test) ∧
      (run.records.any run.test = true ↔ SAT.Satisfiable F) ∧ time ≤ run.bound := by
  obtain ⟨steps, final, hsteps, trace, output⟩ :=
    command_execution run.prefixTrace run.boot run.records run.test run.cost
      run.invariant run.validPayload run.callback run.validRecords run.valid run.source run.payload
  refine ⟨steps + 1, final.withPC none, ?_, rfl, output, run.correct, ?_⟩
  · exact ⟨steps + 1, le_rfl, compiled_execution trace⟩
  · dsimp [bound]
    omega

theorem bound_le (run : Execution p leaf F)
    (prefixLimit setupLimit sparsifyLimit leaves payloadBits leafSteps : ℕ)
    (hp : run.prefixSteps ≤ prefixLimit) (hs : run.boot.setupSteps ≤ setupLimit)
    (ht : run.boot.sparsifySteps ≤ sparsifyLimit) (hl : run.records.length ≤ leaves)
    (hb : ∀ bits ∈ run.records, bits.length ≤ payloadBits)
    (hc : ∀ bits ∈ run.records, run.cost bits ≤ leafSteps) :
    run.bound ≤ prefixLimit + setupLimit + sparsifyLimit + 5 +
      leaves * (6 * payloadBits + leafSteps + 7) := by
  have hrecords := (SubexpMainRuntime.record_budget_le
    run.records run.cost payloadBits leafSteps hb hc).trans
    (Nat.mul_le_mul_right (6 * payloadBits + leafSteps + 7) hl)
  dsimp [bound]
  omega

end Execution

/-- This theorem still requires the actual guarded callback and all its
executions. In particular, it asserts no new SAT algorithm by itself. -/
theorem feasible_of_executions (p : Phases er es) (leaf : MainCmd er es) (width : ℕ)
    {constant exponentConstant : ℝ} {degree : ℕ}
    (hc : 1 ≤ constant) (ha : 0 < exponentConstant) (hd : 0 < degree)
    (large : ∀ᶠ n : ℕ in Filter.atTop, ∀ F : SAT.CNF (Fin n),
      SAT.WidthAtMost width F → ∃ run : Execution p leaf F,
        (run.bound : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
          (Encoding.formulaBitLength F) n) :
    SubexpComputation.Feasible width := by
  apply FinitePrefixProgram.feasible_of_eventually_bounded_program
    (program p leaf) width hc ha hd
  filter_upwards [large] with n hn
  intro F hwidth
  obtain ⟨run, hbound⟩ := hn F hwidth
  obtain ⟨time, final, hrun, hhalt, houtput, hcorrect, htime⟩ := run.runs
  refine ⟨run.records.any run.test, time, final, hrun, hhalt, houtput, hcorrect, ?_⟩
  exact (Nat.cast_le.mpr htime).trans hbound

end SubexponentialSAT.SubexpMainController

end OAI.Algorithms
