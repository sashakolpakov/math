import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticPreparation
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticCleanup
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticStorageBounds

namespace OAI.Algorithms

/-! # The fixed finite program producing the selected irreducible quartic -/

namespace SubexponentialSAT.SubexpQuarticProducer

open BitProgram StructuredCalls SubexpLiftRing SubexpEnumerationPayload SubexpTupleRefinement
open SubexpQuarticProducerControl SubexpQuarticCandidateContract SubexpQuarticStorageBounds

abbrev program := SubexpQuarticProducerControl.program

@[simp] theorem program_input : program.inputStack = 34 := rfl
@[simp] theorem program_output : program.outputStack = 33 := rfl

/-- An explicit polynomial in the prime, the input length, and the binary
word width. All coefficients and exponents are independent of the prime. -/
def preparationBound (p inputLength : ℕ) : ℕ :=
  9 * inputLength + 21 + 2 * (7 * scalarWidth p + 5) +
  (p + 1) * (60 * scalarWidth p + 60) +
  2000 * (p + 1)^4 * (scalarWidth p + 1) + 10 + 110 * (scalarWidth p + 1)

def runtimeBound (p inputLength : ℕ) : ℕ :=
  preparationBound p inputLength +
  (3 + p^4 * (24 * scalarWidth p + callbackCost p + 7)) +
  (68 * workspaceWidth p + 105) + 1

theorem preparation_cost_le (p inputLength : ℕ) [Fact p.Prime] :
    SubexpQuarticPreparation.cost p inputLength ≤ preparationBound p inputLength := by
  have hw : ∀ word ∈ (QuarticSearch.elements p).map (scalarCode p).block,
      word.length ≤ scalarWidth p := by
    intro word hword
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hword
    exact ((scalarCode p).length_block a).le
  have h₂ := SubexpOrderedTupleProgram.cost_two_le _ (scalarWidth p) hw
  have h₄ := SubexpOrderedTupleProgram.cost_four_le _ (scalarWidth p) hw
  simp only [List.length_map, QuarticSearch.length_elements] at h₂ h₄
  have hsum := Nat.add_le_add h₂ h₄
  have htwice :
      1000 * (p + 1)^4 * (scalarWidth p + 1) +
          1000 * (p + 1)^4 * (scalarWidth p + 1) =
        2000 * (p + 1)^4 * (scalarWidth p + 1) := by ring
  rw [htwice] at hsum
  unfold SubexpQuarticPreparation.cost preparationBound
  omega

def outputState (regs : Fin 14 → Bool) (p : ℕ) [Fact p.Prime] : Data :=
  ⟨regs, fun j => if j = 33 then
    encodeTuple (scalarCode p) (QuarticSearch.coefficients p) else []⟩

/-- The input is only the prime's binary bytes. The program itself contains
neither a selected polynomial nor tables depending on the runtime prime. -/
theorem program_runs (p : ℕ) [Fact p.Prime] (bits : List Bool) (regs : Fin 14 → Bool)
    (hvalue : CounterPrograms.value bits = p) :
    ∃ finalRegs,
      RunsIn program (runtimeBound p bits.length)
        ((SubexpQuarticPreparation.inputState regs bits).withPC (some program.entry))
        ((outputState finalRegs p).withPC none) := by
  obtain ⟨n₁, ready, hn₁, he₁, hr, hr28, hr29⟩ :=
    SubexpQuarticPreparation.prepare_eval p bits regs hvalue
  obtain ⟨n₂, selected, hn₂, he₂, hs, hs33, hs28, hs29⟩ :=
    SubexpQuarticCandidateContract.search_eval p (SubexpQuarticPreparation.primeModulus p)
      ready hr hr28 hr29
  have h27 : selected.stacks 27 = [] := hs.2.2.2.2.2.1
  have hwidth := final_workspace p (SubexpQuarticPreparation.primeModulus p) selected hs hs28 hs29
  obtain ⟨n₃, hn₃, he₃⟩ := SubexpQuarticCleanup.cleanup_eval selected (workspaceWidth p) h27 hwidth
  let out := SubexpQuarticCleanup.result selected
  have he : Eval command (n₁ + (n₂ + (n₃ + 0)))
      (SubexpQuarticPreparation.inputState regs bits) out :=
    Eval.seq he₁ (Eval.seq he₂ (Eval.seq he₃ (Eval.base (.skip out))))
  have hout : out = outputState out.regs p := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext j
      by_cases hj : j = 33
      · subst j
        simpa [out, SubexpQuarticCleanup.result, outputState] using hs33
      · simp [out, SubexpQuarticCleanup.result, outputState, hj]
  refine ⟨out.regs, n₁ + (n₂ + (n₃ + 0)) + 1, ?_, ?_⟩
  · have hp := preparation_cost_le p bits.length
    unfold runtimeBound
    omega
  · rw [← hout]
    exact compiled_halt_trace he 34 33

theorem program_runs_toNat (p : ℕ) [Fact p.Prime] (bits : List Bool) (regs : Fin 14 → Bool)
    (hvalue : BinaryArithmetic.toNat bits = p) :
    ∃ finalRegs,
      RunsIn program (runtimeBound p bits.length)
        ((SubexpQuarticPreparation.inputState regs bits).withPC (some program.entry))
        ((outputState finalRegs p).withPC none) :=
  program_runs p bits regs (by simpa only [CounterPrograms.value_eq_toNat] using hvalue)

end SubexponentialSAT.SubexpQuarticProducer

end OAI.Algorithms
