import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJobsStage

namespace OAI.Algorithms

/-! The actual extraction-job stream and its generation cost.  Both the
source service time and its serialized output length occur linearly. -/

namespace SubexponentialSAT.SubexpNodeJobsCostBound

open SubexpOuterJobs SubexpNodeJobsStage
open scoped BigOperators

def scale (D width : ℕ) : ℕ := D + width + 1
def moments (D : ℕ) : ℕ := (3 * D + 1).choose D

private theorem scale_pos (D width : ℕ) : 1 ≤ scale D width := by
  unfold scale
  omega

private theorem moments_pos (D : ℕ) : 1 ≤ moments D :=
  Nat.choose_pos (by omega)

theorem validMoment_length (D : ℕ) (bits : List Bool) (h : ValidMoment D bits) :
    bits.length ≤ 3 * D + 1 := by
  obtain ⟨a, ha, rfl⟩ := h
  have hs := (Algorithm.mem_exponentList D (2 * D + 1) a).mp ha
  simp only [SubexpExponentController.momentWord,
    SubexpSymbolicCost.unaryWords_length_exact, List.sum_ofFn, List.length_ofFn]
  omega

theorem momentMaster_length_le (D width : ℕ) :
    (Encoding.encodeList id (momentRecords D)).length ≤
      7 * scale D width * moments D := by
  have hb := Encoding.length_encodeList_upper id (momentRecords D) (3 * D + 1)
    (fun bits h => validMoment_length D bits (momentRecords_valid D bits h))
  rw [momentRecords_length] at hb
  have hM := moments_pos D
  have hS := scale_pos D width
  change _ ≤ 7 * scale D width * moments D
  have hc : 2 * (3 * D + 1) + 2 ≤ 6 * scale D width := by
    unfold scale
    omega
  have hm := Nat.mul_le_mul_right (moments D) hc
  have ho : 1 ≤ scale D width * moments D := Nat.mul_le_mul hS hM
  change _ ≤ 1 + (2 * (3 * D + 1) + 2) * moments D at hb
  nlinarith only [hb, hm, ho]

theorem job_encode_length (xs source : List Bool) (u z width : ℕ) :
    (SubexpExtractionJobProgram.job xs source u z width).encode.length =
      2 * (z + width + source.length) + 3 := by
  rw [SubexpMomentProgram.Job.encode_length]
  simp [SubexpExtractionJobProgram.job, SubexpJobFrames.job,
    SubexpExtractionJobProgram.normalizedKey, SubexpExponentProgram.padTake_length]

theorem output_length_le (source : List Bool → List Bool) (D width W : ℕ)
    (hsource : ∀ bits, ValidMoment D bits → (source bits).length ≤ W) :
    (output source D width).length ≤
      9 * (scale D width)^3 * (W + 1) * moments D := by
  let S := scale D width
  have hS : 1 ≤ S := scale_pos D width
  have hM := moments_pos D
  have hj : ∀ j ∈ (allJobs source D width (momentRecords D)).reverse,
      j.encode.length ≤ 2 * (D + width + W) + 3 := by
    intro j hj
    rw [List.mem_reverse] at hj
    obtain ⟨bits, hb, hj⟩ := List.mem_flatMap.mp hj
    obtain ⟨z, hz, hj⟩ := List.mem_flatMap.mp hj
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hj
    have hzD := List.mem_range.mp hz
    have hs := hsource bits (momentRecords_valid D bits hb)
    rw [job_encode_length]
    omega
  have hb := Encoding.length_encodeList_upper SubexpMomentProgram.Job.encode
    (allJobs source D width (momentRecords D)).reverse (2 * (D + width + W) + 3) hj
  rw [List.length_reverse, momentJobs_length] at hb
  have hD : D ≤ S := by dsimp [S, scale]; omega
  have hD1 : D + 1 ≤ S := by dsimp [S, scale]; omega
  have hDD : D * (D + 1) ≤ S^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hD hD1
  have hc : 2 * (2 * (D + width + W) + 3) + 2 ≤ 8 * S * (W + 1) := by
    have hSW := Nat.mul_le_mul_right (W + 1) hS
    dsimp [S, scale] at *
    nlinarith only [hSW]
  have hp := Nat.mul_le_mul hc (Nat.mul_le_mul_left (moments D) hDD)
  have ho : 1 ≤ S^3 * (W + 1) * moments D :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow 3 S hS)
      (show 1 ≤ W + 1 by omega)) hM
  change (output source D width).length ≤
    1 + (2 * (2 * (D + width + W) + 3) + 2) * (moments D * (D * (D + 1))) at hb
  change (output source D width).length ≤ 9 * S^3 * (W + 1) * moments D
  nlinarith only [hb, hp, ho]

private theorem callback_full_le (D width T W : ℕ) (bits : List Bool)
    (hbits : bits.length ≤ 3 * D + 1) :
    6 * bits.length + callbackCost D width T W bits + 7 ≤
      1000 * (scale D width)^3 * (T + W + 1) := by
  let S := scale D width
  let U := T + W + 1
  have hS : 1 ≤ S := scale_pos D width
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hD : D ≤ S := by dsimp [S, scale]; omega
  have hD1 : D + 1 ≤ S := by dsimp [S, scale]; omega
  have hb : bits.length ≤ 3 * S := by dsimp [S, scale]; omega
  have hbase : bits.length + W + 2 * D + width + 2 ≤ 6 * S * U := by
    have hSU := Nat.mul_le_mul_right U hS
    have hSU' := Nat.mul_le_mul_left S hU
    dsimp [S, scale, U] at *
    nlinarith only [hbits, hSU, hSU']
  have hproduct : D * (D + 1) * (100 * (bits.length + W + 2 * D + width + 2)) ≤
      600 * (S^3 * U) := by
    calc
      _ ≤ S * S * (100 * (6 * S * U)) := by gcongr
      _ = _ := by ring
  have hS3 : S ≤ S^3 * U := by
    calc
      S = S * 1 := by omega
      _ ≤ S^3 * U := Nat.mul_le_mul (Nat.le_self_pow (by decide) S) hU
  have hS2 : S^2 ≤ S^3 * U := by
    calc
      S^2 = S^2 * 1 := by omega
      _ ≤ S^3 * U := Nat.mul_le_mul (Nat.pow_le_pow_right hS (by decide)) hU
  have hU3 : U ≤ S^3 * U := by
    simpa only [one_mul] using Nat.mul_le_mul_right U (Nat.one_le_pow 3 S hS)
  have hD2 := Nat.pow_le_pow_left hD 2
  have hTU : T ≤ U := by dsimp [U]; omega
  have hWU : W ≤ U := by dsimp [U]; omega
  unfold callbackCost
  change _ ≤ 1000 * S^3 * U
  nlinarith only [hproduct, hb, hS3, hS2, hU3, hD2, hD, hS, hU, hTU, hWU]

private theorem budget_le (cost : List Bool → ℕ) (records : List (List Bool))
    (K : ℕ) (h : ∀ bits ∈ records, 6 * bits.length + cost bits + 7 ≤ K) :
    RecordPrograms.budget cost records ≤ K * records.length := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons bits rest ih =>
      have hh := h bits (by simp)
      have ht := ih (fun b hb => h b (by simp [hb]))
      simp only [RecordPrograms.budget, List.length_cons]
      nlinarith only [hh, ht]

theorem bound_le (source : List Bool → List Bool) (D width T W : ℕ)
    (hsource : ∀ bits, ValidMoment D bits → (source bits).length ≤ W) :
    bound source D width T W ≤
      1100 * (scale D width)^3 * (T + W + 1) * moments D := by
  let K := (scale D width)^3 * (T + W + 1) * moments D
  have hK : 1 ≤ K := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.one_le_pow 3 _ (scale_pos D width))
      (show 1 ≤ T + W + 1 by omega)) (moments_pos D)
  have hb := budget_le (callbackCost D width T W) (momentRecords D)
    (1000 * (scale D width)^3 * (T + W + 1))
    (fun bits h => callback_full_le D width T W bits
      (validMoment_length D bits (momentRecords_valid D bits h)))
  rw [momentRecords_length] at hb
  change RecordPrograms.budget (callbackCost D width T W) (momentRecords D) ≤
    1000 * (scale D width)^3 * (T + W + 1) * moments D at hb
  have ho := output_length_le source D width W hsource
  have hWU : W + 1 ≤ T + W + 1 := by omega
  have hm := Nat.mul_le_mul_right (moments D)
    (Nat.mul_le_mul_left (9 * (scale D width)^3) hWU)
  unfold bound loopBound
  change _ ≤ 1100 * (scale D width)^3 * (T + W + 1) * moments D
  dsimp only [K] at hK
  nlinarith only [hb, ho, hm, hK]

/-- The physical source of the copy is exactly the emitted moment master.
No output-length assumption is used for the generated extraction jobs. -/
theorem masterBound_le (source : List Bool → List Bool) (D width T W : ℕ)
    (d : SubexpNodeJobsStage.Data)
    (hmaster : d.stacks 127 = Encoding.encodeList id (momentRecords D))
    (hsource : ∀ bits, ValidMoment D bits → (source bits).length ≤ W) :
    masterBound source D width T W d ≤
      1200 * (scale D width)^3 * (T + W + 1) * moments D := by
  have hb := bound_le source D width T W hsource
  have hm := momentMaster_length_le D width
  have hS := scale_pos D width
  have hM := moments_pos D
  have hU : 1 ≤ T + W + 1 := by omega
  have hsmall : scale D width * moments D ≤
      (scale D width)^3 * (T + W + 1) * moments D := by
    gcongr
    calc
      scale D width = scale D width * 1 := by omega
      _ ≤ (scale D width)^3 * (T + W + 1) :=
        Nat.mul_le_mul (Nat.le_self_pow (by decide) _) hU
  have hK : 1 ≤ (scale D width)^3 * (T + W + 1) * moments D :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow 3 _ hS) hU) hM
  unfold masterBound
  rw [hmaster]
  nlinarith only [hb, hm, hsmall, hK]

end SubexponentialSAT.SubexpNodeJobsCostBound

end OAI.Algorithms
