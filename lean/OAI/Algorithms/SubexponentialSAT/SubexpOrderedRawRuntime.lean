import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawPrefix
import OAI.Algorithms.SubexponentialSAT.SubexpMainController
import OAI.Algorithms.SubexponentialSAT.SubexpOverhead

namespace OAI.Algorithms

/-!
# Runtime interfaces for the unchanged controller on ordered raw clauses

The source program below is exactly `SubexpMainController.program`. Neither
the clause list nor its size selects a program. The external-input adapter
additionally requires an actual measured preprocessing trace, ending at the
exact initial state for the dense ordered encoding. No remapping, assignment
equivalence, or preprocessing cost is inferred from a semantic function.
-/

namespace SubexponentialSAT.SubexpOrderedRawRuntime

open BitProgram StructuredCalls SubexpMainProgram
open SubexpOrderedRawPrefix (Formula encode bitLength)

variable {er es : ℕ}

structure Execution (p : Phases er es) (leaf : MainCmd er es)
    {n : ℕ} (G : Formula n) where
  afterPrefix : MainState er es
  prefixSteps : ℕ
  prefixTrace : Eval (frontendProcedure er es).invoke prefixSteps
    (initialData er es (encode G)) afterPrefix
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
  correct : records.any test = true ↔ SAT.Satisfiable (ExecCNF.formulaSet G)

namespace Execution

variable {p : Phases er es} {leaf : MainCmd er es} {n : ℕ} {G : Formula n}

def bound (run : Execution p leaf G) : ℕ :=
  run.prefixSteps + run.boot.setupSteps + run.boot.sparsifySteps +
    5 + RecordPrograms.budget run.cost run.records

theorem command_runs (run : Execution p leaf G) :
    ∃ t final, t + 1 ≤ run.bound ∧
      Eval (SubexpMainController.command p leaf) t (initialData er es (encode G)) final ∧
      (final.stacks (persistent es 11)).head? = some (run.records.any run.test) := by
  obtain ⟨t, final, ht, he, ho⟩ := SubexpMainController.command_execution
    run.prefixTrace run.boot run.records run.test run.cost run.invariant
    run.validPayload run.callback run.validRecords run.valid run.source run.payload
  exact ⟨t, final, by dsimp [bound]; omega, he, ho⟩

theorem runs (run : Execution p leaf G) :
    ∃ final, RunsIn (SubexpMainController.program p leaf) run.bound
      (initial (SubexpMainController.program p leaf) (encode G)) final ∧
      final.pc = none ∧
      (final.stacks (SubexpMainController.program p leaf).outputStack).head? =
        some (run.records.any run.test) := by
  obtain ⟨t, final, ht, he, ho⟩ := run.command_runs
  exact ⟨final.withPC none, ⟨t + 1, ht, SubexpMainController.compiled_execution he⟩, rfl, ho⟩

theorem primitive_output (run : Execution p leaf G) :
    (primitive (SubexpMainController.program p leaf)).OutputsInTime (encode G)
      (run.records.any run.test)
      (primitiveOverhead (SubexpMainController.program p leaf) * run.bound) := by
  obtain ⟨final, ht, hh, ho⟩ := run.runs
  exact primitive_outputs_of_halted _ ht hh ho

theorem bound_le (run : Execution p leaf G)
    (prefixLimit setupLimit sparsifyLimit leaves payloadBits leafSteps : ℕ)
    (hp : run.prefixSteps ≤ prefixLimit) (hs : run.boot.setupSteps ≤ setupLimit)
    (ht : run.boot.sparsifySteps ≤ sparsifyLimit) (hl : run.records.length ≤ leaves)
    (hb : ∀ bits ∈ run.records, bits.length ≤ payloadBits)
    (hc : ∀ bits ∈ run.records, run.cost bits ≤ leafSteps) :
    run.bound ≤ prefixLimit + setupLimit + sparsifyLimit + 5 +
      leaves * (6 * payloadBits + leafSteps + 7) := by
  have hrecords := (SubexpMainRuntime.record_budget_le run.records run.cost
    payloadBits leafSteps hb hc).trans
      (Nat.mul_le_mul_right (6 * payloadBits + leafSteps + 7) hl)
  dsimp [bound]
  omega

end Execution

/-- A common source bound transfers to the primitive machine with the
single fixed compiler multiplier. This leaves finite-prefix handling open. -/
theorem eventually_primitive_of_executions (p : Phases er es) (leaf : MainCmd er es)
    (width : ℕ) (constant exponentConstant : ℝ) (degree : ℕ)
    (large : ∀ᶠ n : ℕ in Filter.atTop, ∀ G : Formula n,
      ExecSunflowerSearch.RawWidthAtMost width G → ∃ run : Execution p leaf G,
        (run.bound : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
          (bitLength G) n) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ G : Formula n,
      ExecSunflowerSearch.RawWidthAtMost width G → ∃ answer time,
        (primitive (SubexpMainController.program p leaf)).OutputsInTime (encode G) answer time ∧
        (answer = true ↔ SAT.Satisfiable (ExecCNF.formulaSet G)) ∧
        (time : ℝ) ≤ SubexpComputation.runtimeBound
          ((primitiveOverhead (SubexpMainController.program p leaf) : ℝ) * constant)
          exponentConstant degree (bitLength G) n := by
  filter_upwards [large] with n hn
  intro G hG
  obtain ⟨run, hb⟩ := hn G hG
  refine ⟨run.records.any run.test, primitiveOverhead (SubexpMainController.program p leaf) *
    run.bound, run.primitive_output, run.correct, ?_⟩
  rw [Nat.cast_mul, SubexpComputation.runtimeBound_mul_constant]
  exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)

/-- A fixed preprocessing command followed by the unchanged ordered core. -/
def transportCommand (transport : MainCmd er es) (p : Phases er es) (leaf : MainCmd er es) :
    MainCmd er es := .seq transport (SubexpMainController.command p leaf)

def transportProgram (transport : MainCmd er es) (p : Phases er es) (leaf : MainCmd er es) :=
  compiled (transportCommand transport p leaf) (persistent es 0) (persistent es 11)

/-- No semantic remapping function is executed by this theorem: the caller
must provide its actual trace and exact clean-state handoff. The assignment
equivalence appears separately from that execution premise. -/
theorem transported_primitive_output
    (transport : MainCmd er es) (p : Phases er es) (leaf : MainCmd er es)
    (input : List Bool) {n : ℕ} (G : Formula n) (preprocessSteps : ℕ)
    (preprocess : Eval transport preprocessSteps (initialData er es input)
      (initialData er es (encode G)))
    (run : Execution p leaf G) (meaning : Prop)
    (equivalent : SAT.Satisfiable (ExecCNF.formulaSet G) ↔ meaning) :
    ∃ answer,
      (primitive (transportProgram transport p leaf)).OutputsInTime input answer
        (primitiveOverhead (transportProgram transport p leaf) *
          (preprocessSteps + run.bound)) ∧ (answer = true ↔ meaning) := by
  obtain ⟨t, final, ht, he, ho⟩ := run.command_runs
  have hrun : RunsIn (transportProgram transport p leaf) (preprocessSteps + run.bound)
      (initial (transportProgram transport p leaf) input) (final.withPC none) := by
    refine ⟨preprocessSteps + t + 1, by omega, ?_⟩
    exact compiled_halt_trace (preprocess.seq he) (persistent es 0) (persistent es 11)
  refine ⟨run.records.any run.test, primitive_outputs_of_halted _ hrun rfl ho,
    run.correct.trans equivalent⟩

/-- The actual transport time and actual output length are charged separately.
All constants below are explicit, so a uniform caller must choose them before
its input. A fixed polynomial preprocessing/simulation slowdown preserves the
claimed exponential scale. -/
theorem transported_primitive_bound
    (transport : MainCmd er es) (p : Phases er es) (leaf : MainCmd er es)
    (input : List Bool) {n : ℕ} (G : Formula n) (preprocessSteps : ℕ)
    (preprocess : Eval transport preprocessSteps (initialData er es input)
      (initialData er es (encode G)))
    (run : Execution p leaf G) (meaning : Prop)
    (equivalent : SAT.Satisfiable (ExecCNF.formulaSet G) ↔ meaning)
    (constant exponentConstant sizeConstant : ℝ)
    (degree sizeDegree originalVars power factor : ℕ)
    (hc : 1 ≤ constant) (ha : 0 ≤ exponentConstant) (hs : 1 ≤ sizeConstant)
    (hd : 0 < degree) (he : 0 < sizeDegree) (hp : 0 < power)
    (hsource : (run.bound : ℝ) ≤
      SubexpComputation.runtimeBound constant exponentConstant degree (bitLength G) n)
    (hsize : (bitLength G : ℝ) + 1 ≤
      sizeConstant * ((input.length : ℝ) + 1) ^ sizeDegree)
    (hvars : n ≤ originalVars)
    (hpreprocess : preprocessSteps ≤ factor * (input.length + 1) ^ power) :
    ∃ answer time,
      (primitive (transportProgram transport p leaf)).OutputsInTime input answer time ∧
      (answer = true ↔ meaning) ∧
      (time : ℝ) ≤ SubexpComputation.runtimeBound
        (((primitiveOverhead (transportProgram transport p leaf) * (factor + 1) : ℕ) : ℝ) *
          (2 * (constant * sizeConstant ^ degree)) ^ power)
        ((power : ℝ) * exponentConstant) (sizeDegree * degree * power)
        input.length originalVars := by
  obtain ⟨answer, hout, hanswer⟩ := transported_primitive_output transport p leaf input G
    preprocessSteps preprocess run meaning equivalent
  refine ⟨answer, primitiveOverhead (transportProgram transport p leaf) *
    (preprocessSteps + run.bound), hout, hanswer, ?_⟩
  have hcommon : (run.bound : ℝ) ≤
      SubexpComputation.runtimeBound (constant * sizeConstant ^ degree)
        exponentConstant (sizeDegree * degree) input.length originalVars :=
    hsource.trans (SubexpComputation.polynomial_input_overhead_le (by linarith)
      ha (by linarith) degree sizeDegree input.length (bitLength G) originalVars n hsize hvars)
  have hconstant : 1 ≤ constant * sizeConstant ^ degree :=
    one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ hs)
  have hdegree : 0 < sizeDegree * degree := Nat.mul_pos he hd
  have hbase : input.length + 1 ≤ run.bound + input.length + 1 := by omega
  have hpow := Nat.pow_le_pow_left hbase power
  have hrun : run.bound ≤ (run.bound + input.length + 1) ^ power :=
    (show run.bound ≤ run.bound + input.length + 1 by omega).trans
      (Nat.le_self_pow (by omega) _)
  have htotal : primitiveOverhead (transportProgram transport p leaf) *
        (preprocessSteps + run.bound) ≤
      (primitiveOverhead (transportProgram transport p leaf) * (factor + 1)) *
        (run.bound + input.length + 1) ^ power := by
    have hp' := hpreprocess.trans (Nat.mul_le_mul_left factor hpow)
    calc
      _ ≤ primitiveOverhead (transportProgram transport p leaf) *
          (factor * (run.bound + input.length + 1) ^ power +
            (run.bound + input.length + 1) ^ power) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add hp' hrun)
      _ = _ := by ring
  exact SubexpComputation.nat_polynomial_overhead_le hconstant ha hdegree
    input.length originalVars power
    (primitiveOverhead (transportProgram transport p leaf) * (factor + 1)) run.bound
    (primitiveOverhead (transportProgram transport p leaf) * (preprocessSteps + run.bound))
    hcommon htotal

end SubexponentialSAT.SubexpOrderedRawRuntime

end OAI.Algorithms
