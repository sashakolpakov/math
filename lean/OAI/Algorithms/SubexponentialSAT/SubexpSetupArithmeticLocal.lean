import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SparsificationThresholdProgram
import OAI.Algorithms.SubexponentialSAT.SparsificationBudgetProgram
import OAI.Algorithms.SubexponentialSAT.SubexpIncidenceGuardProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeSelectRuntime
import OAI.Algorithms.SubexponentialSAT.SubexpFieldParameterProgram

namespace OAI.Algorithms

/-!
# Concrete arithmetic phases for the closed setup

The local execution certificates below are extracted from fixed instruction
tables. They retain bounds on the words actually produced, including padding.
The setup-stage wrappers connect these certificates to persistent storage.
-/

namespace SubexponentialSAT.SubexpSetupPhaseArithmetic

open BitProgram StructuredCalls BinaryArithmetic

def selectInput (xs : List Bool) : StructuredProgram.State 3 3 :=
  StructuredProgram.ioState 0 xs

def selectOutput (T : ℕ) (xs : List Bool) : StructuredProgram.State 3 3 :=
  StructuredProgram.ioState 2
    (SparsificationBudgetProgram.outputWord T (CounterPrograms.value xs))

theorem select_local (T : ℕ) (xs : List Bool) :
    ∃ t, Trace (SparsificationBudgetProgram.program T) t
      ((selectInput xs).withPC (some (SparsificationBudgetProgram.program T).entry))
      ((selectOutput T xs).withPC none) ∧
      t ≤ SparsificationBudgetProgram.runtimeBound T xs.length ∧
      BinaryArithmetic.toNat ((selectOutput T xs).stacks 2) =
        SparsificationBudgetProgram.dyadicM T (BinaryArithmetic.toNat xs) ∧
      ((selectOutput T xs).stacks 2).length ≤ T + 2 * xs.length + 3 := by
  obtain ⟨t, ht, he⟩ := SparsificationBudgetProgram.run_correct T xs
  refine ⟨t, he, ht, ?_, SparsificationBudgetProgram.outputWord_length_le T xs⟩
  change BinaryArithmetic.toNat (SparsificationBudgetProgram.outputWord T (CounterPrograms.value xs)) = _
  rw [SparsificationBudgetProgram.outputWord_toNat, SubexpParameterProgram.value_eq_toNat]

def occurrenceInput (k : ℕ) (xs : List Bool) :=
  ArithmeticExpressionProgram.state
    (show 2 ≤ ArithmeticExpressionProgram.slots (SparsificationThresholdProgram.occurrenceExpr k)
      from le_trans (by decide) (ArithmeticExpressionProgram.slots_ge _))
    (fun _ => false) xs []

theorem occurrence_local (k : ℕ) (xs : List Bool) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (word : List Bool),
      Trace (SparsificationThresholdProgram.occurrenceProgram k) t
        ((occurrenceInput k xs).withPC
          (some (SparsificationThresholdProgram.occurrenceProgram k).entry))
        ((ArithmeticExpressionProgram.state
          (show 2 ≤ ArithmeticExpressionProgram.slots (SparsificationThresholdProgram.occurrenceExpr k)
            from le_trans (by decide) (ArithmeticExpressionProgram.slots_ge _))
          rf xs word).withPC none) ∧
      t ≤ (ArithmeticExpressionProgram.timeCoeff (SparsificationThresholdProgram.occurrenceExpr k) + 1) *
        (xs.length + 1) ^ 2 ∧
      BinaryArithmetic.toNat word = SparsificationConstants.occurrenceCap (BinaryArithmetic.toNat xs) k ∧
      word.length ≤ ArithmeticExpressionProgram.widthCoeff
        (SparsificationThresholdProgram.occurrenceExpr k) * (xs.length + 1) := by
  obtain ⟨word, rf, ⟨t, ht, he⟩, hv, hl⟩ :=
    SparsificationThresholdProgram.occurrenceProgram_correct k xs (fun _ => false)
  exact ⟨t, rf, word, he, ht, hv, hl⟩

def incidenceInput (ell cap : List Bool) : SubexpIncidenceGuardProgram.Data :=
  ⟨fun _ => false, ![ell, cap, [], [], [], [], [], [], [], []]⟩

theorem incidence_local (ell cap : List Bool) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (word : List Bool),
      Trace SubexpIncidenceGuardProgram.program t
        ((incidenceInput ell cap).withPC (some SubexpIncidenceGuardProgram.program.entry))
        ((⟨rf, Function.update (incidenceInput ell cap).stacks 2 word⟩ :
          SubexpIncidenceGuardProgram.Data).withPC none) ∧
      t ≤ 300 * (ell.length + cap.length + 3) ^ 2 + 1 ∧
      BinaryArithmetic.toNat word = 1 + BinaryArithmetic.toNat ell * BinaryArithmetic.toNat cap ∧
      word.length ≤ ell.length + cap.length + 3 := by
  have hr : SubexpIncidenceGuardProgram.Ready (incidenceInput ell cap) := by
    intro i hi
    fin_cases i <;> simp_all [incidenceInput]
  obtain ⟨t, rf, word, he, hv, hl, ht⟩ :=
    SubexpIncidenceGuardProgram.command_trace (incidenceInput ell cap) hr
  refine ⟨t + 1, rf, word, he, ?_, hv, hl⟩
  exact Nat.add_le_add_right ht 1

theorem prime_local (exponent : List Bool) :
    ∃ (t : ℕ) (b : SubexpPrimeIntervalProgram.State),
      Trace SubexpPrimeIntervalProgram.primeSelectProgram t
        ((SubexpPrimeIntervalProgram.inputState exponent).withPC
          (some SubexpPrimeIntervalProgram.primeSelectProgram.entry)) (b.withPC none) ∧
      t ≤ SubexpPrimeSelectRuntime.selectorBound exponent + 1 ∧
      BinaryArithmetic.toNat (b.stacks 9) = SubexpPrimeIntervalProgram.selectedPrime (BinaryArithmetic.toNat exponent) ∧
      (b.stacks 9).length ≤ SubexpPrimeSelectRuntime.endpointWordBound exponent +
        (2 ^ BinaryArithmetic.toNat exponent - 1) ∧
      (∀ i, (b.stacks i).length ≤ SubexpPrimeSelectRuntime.selectorWordBound exponent) := by
  obtain ⟨t, b, he, ht, hv, hl⟩ := SubexpPrimeSelectRuntime.primeSelect_bounded exponent
  refine ⟨t + 1, b, compiled_halt_trace he 0 9, Nat.add_le_add_right ht 1, ?_, ?_,
    SubexpPrimeSelectRuntime.primeSelect_all_words exponent he⟩
  · simpa only [SubexpParameterProgram.value_eq_toNat] using hv
  · simpa only [SubexpParameterProgram.value_eq_toNat] using hl

def fieldInput (p delta : List Bool) : SubexpFieldParameterProgram.Data :=
  SubexpFieldParameterProgram.state (fun _ => false)
    (SubexpFieldParameterProgram.inputWords p delta)

theorem field_local (k : ℕ) (hk : 0 < k) (p delta : List Bool)
    (hp : 0 < BinaryArithmetic.toNat p) (hd : 0 < BinaryArithmetic.toNat delta) :
    ∃ (t : ℕ) (b : SubexpFieldParameterProgram.Data),
      Trace (SubexpFieldParameterProgram.program k) t
        ((fieldInput p delta).withPC (some (SubexpFieldParameterProgram.program k).entry))
        (b.withPC none) ∧
      t ≤ 30000 * (SubexpFieldParameterProgram.width k p delta) ^ 2 ∧
      BinaryArithmetic.toNat (b.stacks 4) = BinaryArithmetic.toNat p ^ 4 - 1 ∧
      BinaryArithmetic.toNat (b.stacks 7) = (BinaryArithmetic.toNat p ^ 4 - 1) / (8 * BinaryArithmetic.toNat delta * k * BinaryArithmetic.toNat p) ∧
      (∀ i, (b.stacks i).length ≤ 4 * SubexpFieldParameterProgram.width k p delta) := by
  obtain ⟨b, _, _, hQ, _, hR, hlen, _, t, ht, he⟩ :=
    SubexpFieldParameterProgram.run_value k hk (fun _ => false) p delta hp hd
  exact ⟨t, b, he, ht, hQ, hR, hlen⟩

end SubexponentialSAT.SubexpSetupPhaseArithmetic

end OAI.Algorithms
