import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram
import OAI.Algorithms.SubexponentialSAT.FinitePrefixProgram

namespace OAI.Algorithms

/-!
# From the executed main phases to the uniform SAT bound

An `Execution` supplies traces of the actual fixed phase programs, their
physical interfaces, and the leaf coverage theorem. Its bound includes the
parser, every leaf callback, output, and halt. The completion theorem then
adds the already implemented finite-input fallback and primitive simulation.

The phase traces and their uniform bound must still be proved for a concrete
`Phases` value. This module does not assert that such an implementation exists.
-/

namespace SubexponentialSAT.SubexpMainRuntime

open SubexpMainProgram

variable {er es : ℕ}

/-- All interfaces needed to execute the complete main control graph on one
input. The fields describing costs accompany actual instruction traces. -/
structure Execution (p : Phases er es) {n : ℕ} (F : SAT.CNF (Fin n)) where
  afterPrefix : MainState er es
  prefixSteps : ℕ
  prefixTrace : StructuredCalls.Eval (frontendProcedure er es).invoke prefixSteps
    (initialData er es (Encoding.encodeCNF F)) afterPrefix
  boot : BootRun p afterPrefix
  records : List (List Bool)
  test : List Bool → Bool
  cost : List Bool → ℕ
  invariant : MainState er es → Prop
  validPayload : List Bool → Prop
  leaf : LeafContract p test cost invariant validPayload
  validRecords : ∀ bits ∈ records, validPayload bits
  valid : invariant boot.afterSparsify
  source : boot.afterSparsify.stacks (persistent es 7) = Encoding.encodeList id records
  payload : boot.afterSparsify.stacks (persistent es 8) = []
  correct : records.any test = true ↔ SAT.Satisfiable F

namespace Execution

variable {p : Phases er es} {n : ℕ} {F : SAT.CNF (Fin n)}

/-- The additional five instructions include the iterator overhead, the final
answer push, and the compiled halt, as counted by `command_execution`. -/
def bound (run : Execution p F) : ℕ :=
  run.prefixSteps + run.boot.setupSteps + run.boot.sparsifySteps +
    5 + RecordPrograms.budget run.cost run.records

theorem runs (run : Execution p F) :
    ∃ (time : ℕ) (final : BitProgram.Cfg (totalRegs er) (totalStacks es)
        (StructuredCalls.size (command p) + 1)),
      BitProgram.RunsIn (program p) time
        (BitProgram.initial (program p) (Encoding.encodeCNF F)) final ∧
      final.pc = none ∧
      (final.stacks (program p).outputStack).head? = some (run.records.any run.test) ∧
      (run.records.any run.test = true ↔ SAT.Satisfiable F) ∧ time ≤ run.bound := by
  obtain ⟨steps, final, hsteps, trace, output⟩ :=
    command_execution run.prefixTrace run.boot run.records run.test run.cost
      run.invariant run.validPayload run.leaf run.validRecords run.valid run.source run.payload
  refine ⟨steps + 1, final.withPC none, ?_, rfl, output, run.correct, ?_⟩
  · exact ⟨steps + 1, le_rfl, compiled_execution trace⟩
  · dsimp [bound]
    omega

end Execution

/-- Charge all encoded payloads, including leaves after a possible early
success. This upper bound never assumes that leaf answers partition SAT. -/
theorem record_budget_le (records : List (List Bool)) (cost : List Bool → ℕ)
    (payloadBits leafSteps : ℕ)
    (hbits : ∀ bits ∈ records, bits.length ≤ payloadBits)
    (hcost : ∀ bits ∈ records, cost bits ≤ leafSteps) :
    RecordPrograms.budget cost records ≤
      records.length * (6 * payloadBits + leafSteps + 7) := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons bits rest ih =>
      have hb := hbits bits (by simp)
      have hc := hcost bits (by simp)
      have ht := ih (fun b h => hbits b (by simp [h]))
        (fun b h => hcost b (by simp [h]))
      simp only [RecordPrograms.budget, List.length_cons]
      nlinarith

/-- A direct numerical bound in the measured costs of setup, sparsification,
and the number, size, and processing cost of the resulting leaves. -/
theorem execution_bound_le {p : Phases er es} {n : ℕ} {F : SAT.CNF (Fin n)}
    (run : Execution p F) (prefixLimit setupLimit sparsifyLimit leaves payloadBits leafSteps : ℕ)
    (hp : run.prefixSteps ≤ prefixLimit) (hs : run.boot.setupSteps ≤ setupLimit)
    (ht : run.boot.sparsifySteps ≤ sparsifyLimit) (hl : run.records.length ≤ leaves)
    (hb : ∀ bits ∈ run.records, bits.length ≤ payloadBits)
    (hc : ∀ bits ∈ run.records, run.cost bits ≤ leafSteps) :
    run.bound ≤ prefixLimit + setupLimit + sparsifyLimit + 5 +
      leaves * (6 * payloadBits + leafSteps + 7) := by
  have hrecords := (record_budget_le run.records run.cost payloadBits leafSteps hb hc).trans
    (Nat.mul_le_mul_right (6 * payloadBits + leafSteps + 7) hl)
  dsimp [Execution.bound]
  omega

/-- Actual phase executions with an eventual uniform source bound suffice for
the requested primitive-machine theorem. The machine, constants, and finite
fallback cutoff are all fixed before the varying input. -/
theorem feasible_of_executions (p : Phases er es) (width : ℕ)
    {constant exponentConstant : ℝ} {degree : ℕ}
    (hc : 1 ≤ constant) (ha : 0 < exponentConstant) (hd : 0 < degree)
    (large : ∀ᶠ n : ℕ in Filter.atTop, ∀ F : SAT.CNF (Fin n),
      SAT.WidthAtMost width F → ∃ run : Execution p F,
        (run.bound : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
          (Encoding.formulaBitLength F) n) :
    SubexpComputation.Feasible width := by
  apply FinitePrefixProgram.feasible_of_eventually_bounded_program (program p) width hc ha hd
  filter_upwards [large] with n hn
  intro F hwidth
  obtain ⟨run, hbound⟩ := hn F hwidth
  obtain ⟨time, final, hrun, hhalt, houtput, hcorrect, htime⟩ := run.runs
  refine ⟨run.records.any run.test, time, final, hrun, hhalt, houtput, hcorrect, ?_⟩
  exact (Nat.cast_le.mpr htime).trans hbound

end SubexponentialSAT.SubexpMainRuntime

end OAI.Algorithms
