import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayloadValid
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectTuple
import OAI.Algorithms.SubexponentialSAT.SubexpAlphabetProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamilyPayload

open HashFamily

theorem alphabetWords_eq {m : ℕ} (countWord : List Bool)
    (hv : CounterPrograms.value countWord = 3 * m) :
    SubexpAlphabetProgram.alphabetWords countWord = alphabet m countWord.length := by
  simp [SubexpAlphabetProgram.alphabetWords, alphabet, hv]

theorem countWord_width_sufficient {m : ℕ} (countWord : List Bool)
    (hv : CounterPrograms.value countWord = 3 * m) :
    3 * m < 2 ^ countWord.length := by
  have h := ModularArithmetic.toNat_lt_pow_length countWord
  simpa only [← CounterPrograms.value_eq_toNat countWord, hv] using h

/-- Initial code rows may have more chunks than candidate hash rows. The
shared matrix decoder therefore obtains each row's depth from its payload. -/
def decodeVariableRow (m width : ℕ) (payload : List Bool) : Fin m → ZMod 3 :=
  decodeRow m (payload.length / width) width payload

theorem width_pos {m width : ℕ} (hm : 0 < m) (hw : 3 * m ≤ 2 ^ width) :
    0 < width := by
  by_contra h
  have hz : width = 0 := by omega
  simp only [hz, pow_zero] at hw
  omega

theorem decodeVariableRow_generated {m width depth : ℕ} (hm : 0 < m)
    (hw : 3 * m ≤ 2 ^ width) (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth) :
    decodeVariableRow m width payload = decodeRow m depth width payload := by
  unfold decodeVariableRow
  rw [generated_payload_width m width depth payload hp,
    Nat.mul_div_cancel depth (width_pos hm hw)]

theorem decodeVariableRow_encode {m depth width : ℕ} (hm : 0 < m)
    (hw : 3 * m ≤ 2 ^ width) (h : Candidate m depth) :
    decodeVariableRow m width (encode width h) = row h := by
  rw [decodeVariableRow_generated hm hw _ (encode_mem width h)]
  exact decodeRow_encode hm width hw h

theorem generated_tupleFamily_coverage {m depth c : ℕ} (hm : 0 < m)
    (hcount : (3 * m) ^ depth = c + 1) (width : ℕ) (hw : 3 * m ≤ 2 ^ width) :
    ∀ i : Fin (c + 1),
      ∃ payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth,
        decodeRow m depth width payload = HashSelect.tupleFamily hcount i := by
  intro i
  exact generated_coverage hm width hw
    (enumerate m depth (Fin.cast hcount.symm i))

/-- Direct input to the list-selector correctness theorem. -/
theorem list_tupleFamily_coverage {m depth c : ℕ} (hm : 0 < m)
    (hcount : (3 * m) ^ depth = c + 1) (width : ℕ) (hw : 3 * m ≤ 2 ^ width)
    (seed : List Bool) (rest : List (List Bool))
    (hlist : HashSelectProgram.generatedPayloads (alphabet m width) depth = seed :: rest) :
    ∀ i : Fin (c + 1), ∃ payload ∈ seed :: rest,
      decodeRow m depth width payload = HashSelect.tupleFamily hcount i := by
  simpa only [hlist] using generated_tupleFamily_coverage hm hcount width hw

theorem generated_variable_coverage {m depth : ℕ} (hm : 0 < m)
    (width : ℕ) (hw : 3 * m ≤ 2 ^ width) (h : Candidate m depth) :
    ∃ payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth,
      decodeVariableRow m width payload = row h :=
  ⟨encode width h, encode_mem width h, decodeVariableRow_encode hm hw h⟩

theorem list_variable_tupleFamily_coverage {m depth c : ℕ} (hm : 0 < m)
    (hcount : (3 * m) ^ depth = c + 1) (width : ℕ) (hw : 3 * m ≤ 2 ^ width)
    (seed : List Bool) (rest : List (List Bool))
    (hlist : HashSelectProgram.generatedPayloads (alphabet m width) depth = seed :: rest) :
    ∀ i : Fin (c + 1), ∃ payload ∈ seed :: rest,
      decodeVariableRow m width payload = HashSelect.tupleFamily hcount i := by
  intro i
  simpa only [hlist, HashSelect.tupleFamily, HashSelect.tupleRows] using
    generated_variable_coverage hm width hw
    (enumerate m depth (Fin.cast hcount.symm i))

theorem decoded_rowSupport_le (m depth width : ℕ) (payload : List Bool) :
    (HashInput.rowSupport (decodeRow m depth width payload)).card ≤ depth := by
  rw [HashSelect.rowSupport_card_eq_supportCard]
  exact decodeRow_support m depth width payload

end SubexponentialSAT.SqrtLog.HashFamilyPayload

end OAI.Algorithms
