import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisComplementColumns

namespace OAI.Algorithms

/-! Polynomial bounds for the actual color-loop traces. All size parameters
are lengths of stored unary fields and framed local-table records. -/

namespace SubexponentialSAT.Subexp.GlobalBasisComplementColumns

theorem payload_fields_le (q : LocalData) :
    q.N + q.rank + q.table.length ≤ q.payload.length := by
  simp [LocalData.payload, SubexpLocalBatchParse.payload, SubexpLocalBatchParse.unary]
  omega

theorem stepCost_bound (block color : ℕ) (q : LocalData) :
    stepCost block color q ≤ 400 * (block + color + q.payload.length + 1)^2 := by
  have hp := payload_fields_le q
  have hparse := SubexpLocalBatchParse.cost_le_payload q.N q.rank q.table
  change SubexpLocalBatchParse.cost q.N q.rank q.table ≤ 17 * q.payload.length + 8 at hparse
  have hseg := GlobalBasisColumns.segmentCost_polynomial block color q.rank (q.N - q.rank)
  have hi : block + color + q.rank + (q.N - q.rank) + 1 ≤
      block + color + q.payload.length + 1 := by omega
  have hseg' : GlobalBasisColumns.segmentCost block color q.rank (q.N - q.rank) + 1 ≤
      200 * (block + color + q.payload.length + 1)^2 :=
    hseg.trans (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left hi 2))
  let B := block + color + q.payload.length + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hP : q.payload.length ≤ B := by dsimp [B]; omega
  have hB2 : B ≤ B^2 := by nlinarith
  change stepCost block color q ≤ 400 * B^2
  change GlobalBasisColumns.segmentCost block color q.rank (q.N - q.rank) + 1 ≤
      200 * B^2 at hseg'
  unfold stepCost
  nlinarith

theorem member_payload_le {q : LocalData} {qs : List LocalData} (hq : q ∈ qs) :
    q.payload.length ≤ (encoded qs).length := by
  induction qs with
  | nil => simp at hq
  | cons x xs ih =>
    rcases List.mem_cons.mp hq with rfl | hq
    · simp [encoded, Encoding.encodeList]
      omega
    · have h := ih hq
      simp [encoded, Encoding.encodeList] at *
      omega

theorem count_le_encoded (qs : List LocalData) : qs.length ≤ (encoded qs).length := by
  induction qs with
  | nil => simp [encoded, Encoding.encodeList]
  | cons q qs ih => simp [encoded, Encoding.encodeList] at *; omega

theorem colorCost_le_uniform (block limit : ℕ) (qs : List LocalData)
    (hlen : qs.length ≤ limit) (hpayload : ∀ q ∈ qs, q.payload.length ≤ limit) :
    colorCost block qs ≤ qs.length * (400 * (block + 2 * limit + 1)^2 + 2) + 2 := by
  induction qs with
  | nil => simp [colorCost]
  | cons q qs ih =>
    have hqs : qs.length ≤ limit := by simpa only [List.length_cons] using Nat.le_of_succ_le hlen
    have hs := ih hqs (fun x hx => hpayload x (by simp [hx]))
    have hp := hpayload q (by simp)
    have hb := (stepCost_bound block qs.length q).trans
      (Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left
        (show block + qs.length + q.payload.length + 1 ≤ block + 2 * limit + 1 by omega) 2))
    simp only [colorCost, List.length_cons]
    nlinarith

theorem colorCost_polynomial (block : ℕ) (qs : List LocalData) :
    colorCost block qs + 1 ≤ 500 * (block + 2 * (encoded qs).length + 1)^3 := by
  let B := block + 2 * (encoded qs).length + 1
  have hs := colorCost_le_uniform block (encoded qs).length qs
    (count_le_encoded qs) (fun q hq => member_payload_le hq)
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hcount : qs.length ≤ B := (count_le_encoded qs).trans (by dsimp [B]; omega)
  have hB2 : B ≤ B^2 := by nlinarith
  have hB3 : B^2 ≤ B^3 := by nlinarith [Nat.mul_le_mul_right B hB2]
  have hm := Nat.mul_le_mul_right (400 * B^2 + 2) hcount
  change colorCost block qs ≤ qs.length * (400 * B^2 + 2) + 2 at hs
  change colorCost block qs + 1 ≤ 500 * B^3
  nlinarith

end SubexponentialSAT.Subexp.GlobalBasisComplementColumns

end OAI.Algorithms
