import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHash
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramResources

namespace OAI.Algorithms

/-! Output-sensitive numeric costs for the complete native hash controller.
The candidate-family term is quadratic in its actual number of records;
mass evaluation is still charged separately on every tested record. -/

namespace SubexponentialSAT.SqrtLog.Execution.Hash

open HashSelectProgram

def polynomialBudget (count depth rounds : List Bool) (B C cost : ℕ) : ℕ :=
  let A := CounterPrograms.value count
  let P := CounterPrograms.value depth
  let K := CounterPrograms.value rounds
  let w := count.length
  HashInputs.budget count depth rounds +
    400 * (P+1) * A^2 * (A^P)^2 * ((P+1)*w+1) + 15 +
    controllerBudget B C cost (1 + (2*(P*w)+2)*(A^P)) (A^P) K

theorem budget_le_polynomial (count depth rounds : List Bool) (B C cost : ℕ)
    (hcount : 2 ≤ CounterPrograms.value count) :
    budget count depth rounds B C cost ≤ polynomialBudget count depth rounds B C cost := by
  let alphabet := SubexpAlphabetProgram.alphabetWords count
  have hlen : alphabet.length = CounterPrograms.value count := by
    simp [alphabet, SubexpAlphabetProgram.alphabetWords]
  have hw : ∀ x ∈ alphabet, x.length = count.length := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    simp
  have henum := generated_cost_polynomial alphabet count.length (CounterPrograms.value depth)
    (by simpa only [hlen] using hcount) (fun x hx => (hw x hx).le)
  have hwidth := generatedPayloads_width alphabet count.length (CounterPrograms.value depth) hw
  have hfamily := candidateEncoding_length_le
    (generatedPayloads alphabet (CounterPrograms.value depth))
    (CounterPrograms.value depth * count.length) (fun x hx => (hwidth x hx).le)
  have hsize : (generatedPayloads alphabet (CounterPrograms.value depth)).length =
      CounterPrograms.value count ^ CounterPrograms.value depth := by
    rw [generatedPayloads_length, hlen]
  rw [hlen] at henum
  rw [hsize] at hfamily
  have hcontroller : controllerBudget B C cost
      (candidateEncoding (generatedPayloads alphabet (CounterPrograms.value depth))).length
      (generatedPayloads alphabet (CounterPrograms.value depth)).length (CounterPrograms.value rounds) ≤
      controllerBudget B C cost
        (1+(2*(CounterPrograms.value depth*count.length)+2)*
          (CounterPrograms.value count^CounterPrograms.value depth))
        (CounterPrograms.value count^CounterPrograms.value depth) (CounterPrograms.value rounds) := by
    rw [hsize]
    unfold controllerBudget roundsBudget roundBudget
    gcongr
  dsimp only [budget, HashSetup.budget, polynomialBudget]
  change HashInputs.budget count depth rounds +
      Subexp.TupleProgram.powerCost alphabet (CounterPrograms.value depth) [[]] + 14 + 1 +
      controllerBudget B C cost _ _ _ ≤ _
  dsimp only [alphabet] at *
  omega

end SubexponentialSAT.SqrtLog.Execution.Hash

end OAI.Algorithms
