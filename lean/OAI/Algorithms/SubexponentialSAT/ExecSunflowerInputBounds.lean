import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CandidatePrepareBounds

namespace OAI.Algorithms

/-! Actual input-bit bounds for the masked-candidate callback. -/

namespace SubexponentialSAT.ExecSunflowerCallbackBounds

open CandidatePrepareProgram

def aggregate (F : Formula) (k r w : ℕ) (limit width size : List Bool) : ℕ :=
  (formulaCode F).length + k + r + w + limit.length + width.length + size.length + 1

theorem tupleCode_length (words : List (List Bool)) :
    (tupleCode words).length = 2 * (words.map List.length).sum + 2 * words.length + 1 := by
  induction words with
  | nil => rfl
  | cons x xs ih =>
    simp only [tupleCode, Encoding.length_encodeList_cons, id_eq, List.map_cons,
      List.sum_cons, List.length_cons] at *
    omega

theorem maskedTuple_length (mask : List Bool) (words : List (List Bool)) (k r w : ℕ)
    (hm : mask.length = k) (hw : words.map List.length = List.replicate r w) :
    (tupleCode (mask :: words)).length = 2 * (k + r * w) + 2 * (r + 1) + 1 := by
  have hl : words.length = r := by simpa using congrArg List.length hw
  rw [tupleCode_length]
  simp only [List.map_cons, List.sum_cons, hm, hw, List.sum_replicate, smul_eq_mul,
    List.length_cons, hl]

theorem selected_mem (F : Formula) (words : List (List Bool)) (C : Clause)
    (hC : C ∈ selected F words) : C ∈ F := by
  have h := List.mem_reverse.mp hC
  obtain ⟨bits, _, hb⟩ := List.mem_filterMap.mp h
  exact List.mem_of_getElem? hb

theorem selected_bits_le (F : Formula) (words : List (List Bool)) :
    (formulaCode (selected F words)).length ≤
      1 + (2 * (formulaCode F).length + 2) * words.length := by
  have hC : ∀ C ∈ selected F words, (clauseCode C).length ≤ (formulaCode F).length := by
    intro C hC
    exact ExecSelectedFamilySize.member_encoded_length_le clauseCode F C
      (selected_mem F words C hC)
  have hb := Encoding.length_encodeList_upper clauseCode (selected F words)
    (formulaCode F).length hC
  have hl : (selected F words).length ≤ words.length := by
    simpa only [selected, List.length_reverse, ExecSelectedFamilyProgram.selectedClauses] using
      List.length_filterMap_le (fun bits => F[CounterPrograms.value bits]?) words
  exact hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) 1)

theorem core_bits_le (F : Formula) (mask : List Bool) (words : List (List Bool)) :
    (clauseCode (core F mask words)).length ≤ (formulaCode F).length := by
  have hh : (clauseCode ((selected F words).headD [])).length ≤ (formulaCode F).length := by
    cases hs : selected F words with
    | nil =>
      have hf := Encoding.length_encodeList_lower clauseCode F
      simp only [ List.headD_nil, clauseCode, Encoding.length_encodeList_nil]
      change F.length + 1 ≤ (formulaCode F).length at hf
      omega
    | cons C Cs =>
      have hc := ExecSelectedFamilySize.member_encoded_length_le clauseCode F C
        (selected_mem F words C (by rw [hs]; simp))
      simpa only [hs, List.headD_cons, formulaCode] using hc
  exact (CoreMaskProgram.selected_encoded_length_le mask ((selected F words).headD [])).trans hh

end SubexponentialSAT.ExecSunflowerCallbackBounds

end OAI.Algorithms
