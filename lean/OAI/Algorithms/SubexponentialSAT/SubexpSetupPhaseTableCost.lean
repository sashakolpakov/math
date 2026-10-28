import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseTable
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeProgram

namespace OAI.Algorithms

/-! Full storage and callee cost of the fixed threshold-table setup phase. -/

namespace SubexponentialSAT.SubexpSetupPhaseTable

open BitProgram StructuredCalls SubexpSetupProgram SubexpSetupStorage

def tableWordCoeff (c : Config) : ℕ :=
  SparsificationThresholdTable.widthCoeff (SparsificationThresholdTable.expressions c.k) + 1

def tableStorageCoeff (c : Config) : ℕ :=
  6 * tableSlots c + 7 + 10 * thresholdCount c + 21

def tablePolynomialCoeff (c : Config) : ℕ :=
  SparsificationThresholdTable.timeCoeff (SparsificationThresholdTable.expressions c.k) +
    tableStorageCoeff c * (tableWordCoeff c + 1) + tableWordCoeff c + 1

theorem tablePolynomialCoeff_pos (c : Config) : 1 ≤ tablePolynomialCoeff c := by
  unfold tablePolynomialCoeff
  omega

theorem tableOut_wordBound (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (words : Fin (thresholdCount c) → List Bool) (K : ℕ)
    (hM : (a.stacks (persistent c 23)).length ≤ K)
    (hwords : ∀ i, (words i).length ≤ K) :
    WordBound K (tableOut c a rf words) := by
  intro j
  refine Fin.addCases (fun w => ?_) (fun i => ?_) j
  · change (Fin.append _ words (Fin.castAdd (thresholdCount c) w)).length ≤ K
    rw [Fin.append_left]
    by_cases h0 : w = SparsificationThresholdTable.workInput
        (SparsificationThresholdTable.expressions c.k)
    · subst w
      simpa only [SparsificationThresholdTable.workInput,
        ArithmeticExpressionProgram.state_input] using hM
    · by_cases h1 : w = SparsificationThresholdTable.workOutput
          (SparsificationThresholdTable.expressions c.k)
      · subst w
        simp only [SparsificationThresholdTable.workOutput,
          ArithmeticExpressionProgram.state_output, List.length_nil, Nat.zero_le]
      · rw [ArithmeticExpressionProgram.state_other _ _ _ _ w h0 h1]
        exact Nat.zero_le K
  · change (Fin.append _ words
      (Fin.natAdd (SparsificationThresholdTable.workSlots
        (SparsificationThresholdTable.expressions c.k)) i)).length ≤ K
    rw [Fin.append_right]
    exact hwords i

/-- The exact phase terminates with polynomial time and a polynomial bound on
every output stack, starting from a bound on every actual input stack. -/
theorem thresholdTable_bounded_witness (c : Config) (B : ℕ) (a : SetupState c)
    (ha : WordBound B a) :
    ∃ t b, Eval (thresholdTable c) t a b ∧
      t ≤ tablePolynomialCoeff c * (B + 1)^2 ∧
      WordBound (tablePolynomialCoeff c * (B + 1)^2) b := by
  obtain ⟨u, rf, words, hu, he, _, hsum, _⟩ := table_eval c a
  let K := tableWordCoeff c * (B + 1)
  have hR : 1 ≤ tableWordCoeff c := by unfold tableWordCoeff; omega
  have hBK : B ≤ K := by
    calc
      B ≤ B + 1 := by omega
      _ = 1 * (B + 1) := by simp
      _ ≤ tableWordCoeff c * (B + 1) := Nat.mul_le_mul_right _ hR
  have haK : WordBound K a := fun i => (ha i).trans hBK
  have hM : (a.stacks (persistent c 23)).length + 1 ≤ B + 1 :=
    Nat.add_le_add_right (ha _) 1
  have hsum' : (∑ i, (words i).length) ≤
      SparsificationThresholdTable.widthCoeff (SparsificationThresholdTable.expressions c.k) *
        (B + 1) := by
    have hs : (∑ i, (words i).length) ≤
        SparsificationThresholdTable.widthCoeff (SparsificationThresholdTable.expressions c.k) *
          ((a.stacks (persistent c 23)).length + 1) := by
      change (∑ i : Fin (thresholdCount c), (words i).length) ≤ _
      calc
        _ = ∑ i : Fin (thresholdCount c),
            ((tableResult c a rf words).stacks (threshold c i)).length := by
              apply Finset.sum_congr rfl
              intro i _
              rw [table_result_word]
        _ ≤ _ := hsum
    exact hs.trans (Nat.mul_le_mul_left _ hM)
  have hwords : ∀ i, (words i).length ≤ K := by
    intro i
    have hi : (words i).length ≤ ∑ j, (words j).length :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (words j).length) (Finset.mem_univ i)
    apply (hi.trans hsum').trans
    exact Nat.mul_le_mul_right (B + 1) (by unfold tableWordCoeff; omega)
  have hout : WordBound K (tableOut c a rf words) :=
    tableOut_wordBound c a rf words K ((ha _).trans hBK) hwords
  have hcost := stageCost_le c (registerPort (by decide : 8 ≤ 9)) (tableFit c)
    (tableInputs c) (tableOutputs c) a (tableOut c a rf words) u K
    (table_inputs_protected c) (table_outputs_protected c)
    (List.nodup_singleton _) (table_outputs_nodup c) haK hout
  have hcost' : tableCost c a rf words u ≤
      u + storageOverhead (tableSlots c) 1 (thresholdCount c) K := by
    simpa only [tableCost, tableInputs, tableOutputs, List.length_singleton,
      List.length_ofFn] using hcost
  have hreturned : WordBound K (tableResult c a rf words) :=
    returned_wordBound c (registerPort (by decide : 8 ≤ 9)) (tableFit c)
      (tableInputs c) (tableOutputs c) a (tableOut c a rf words) K
      (table_inputs_protected c) (table_outputs_protected c)
      (List.nodup_singleton _) (table_outputs_nodup c) haK hout
  have hlocal : u ≤
      SparsificationThresholdTable.timeCoeff (SparsificationThresholdTable.expressions c.k) *
        (B + 1)^2 :=
    hu.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 2))
  have hsq : B + 1 ≤ (B + 1)^2 := by nlinarith
  have hKplus : K + 1 ≤ (tableWordCoeff c + 1) * (B + 1) := by
    calc
      K + 1 ≤ K + (B + 1) := Nat.add_le_add_left (by omega) K
      _ = (tableWordCoeff c + 1) * (B + 1) := by dsimp [K]; ring
  have hover : storageOverhead (tableSlots c) 1 (thresholdCount c) K ≤
      (tableStorageCoeff c * (tableWordCoeff c + 1)) * (B + 1)^2 := by
    calc
      storageOverhead (tableSlots c) 1 (thresholdCount c) K ≤
          tableStorageCoeff c * (K + 1) := by
        simpa only [tableStorageCoeff, Nat.mul_one] using
          storageOverhead_linear (tableSlots c) 1 (thresholdCount c) K
      _ ≤ tableStorageCoeff c * ((tableWordCoeff c + 1) * (B + 1)) :=
        Nat.mul_le_mul_left _ hKplus
      _ ≤ tableStorageCoeff c * ((tableWordCoeff c + 1) * (B + 1)^2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsq)
      _ = _ := by ring
  have htotal : tableCost c a rf words u ≤ tablePolynomialCoeff c * (B + 1)^2 := by
    calc
      tableCost c a rf words u ≤ u +
          storageOverhead (tableSlots c) 1 (thresholdCount c) K := hcost'
      _ ≤
          SparsificationThresholdTable.timeCoeff (SparsificationThresholdTable.expressions c.k) *
              (B + 1)^2 +
            (tableStorageCoeff c * (tableWordCoeff c + 1)) * (B + 1)^2 :=
        Nat.add_le_add hlocal hover
      _ = (SparsificationThresholdTable.timeCoeff
          (SparsificationThresholdTable.expressions c.k) +
            tableStorageCoeff c * (tableWordCoeff c + 1)) * (B + 1)^2 := by ring
      _ ≤ tablePolynomialCoeff c * (B + 1)^2 :=
        Nat.mul_le_mul_right _ (by unfold tablePolynomialCoeff; omega)
  have hKbound : K ≤ tablePolynomialCoeff c * (B + 1)^2 := by
    calc
      K ≤ tableWordCoeff c * (B + 1)^2 := Nat.mul_le_mul_left _ hsq
      _ ≤ tablePolynomialCoeff c * (B + 1)^2 :=
        Nat.mul_le_mul_right _ (by unfold tablePolynomialCoeff; omega)
  exact ⟨tableCost c a rf words u, tableResult c a rf words, he, htotal,
    fun i => (hreturned i).trans hKbound⟩

/-- Uniform bound for every actual execution; all coefficients precede the
runtime word bound, the auxiliary parameter, and the complete input state. -/
theorem thresholdTable_polynomial (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧
      ∀ (B P : ℕ) (a : SetupState c) (t : ℕ) (b : SetupState c),
        WordBound B a → Eval (thresholdTable c) t a b →
          t ≤ C * (B + P + 1)^q ∧ WordBound (C * (B + P + 1)^q) b := by
  refine ⟨tablePolynomialCoeff c, 2, tablePolynomialCoeff_pos c, by decide, ?_⟩
  intro B P a t b ha he
  obtain ⟨u, out, hu, htime, hout⟩ := thresholdTable_bounded_witness c B a ha
  have ht := SubexpPrimeProgram.eval_steps_unique he hu (persistent c 0) (persistent c 0)
  have hb := SubexpPrimeProgram.eval_result_unique he hu (persistent c 0) (persistent c 0)
  have henv : tablePolynomialCoeff c * (B + 1)^2 ≤
      tablePolynomialCoeff c * (B + P + 1)^2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  constructor
  · rw [ht]
    exact htime.trans henv
  · rw [hb]
    exact fun i => (hout i).trans henv

end SubexponentialSAT.SubexpSetupPhaseTable

end OAI.Algorithms
