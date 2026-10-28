import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramBounded

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.Subexp

/-- At least two alphabet symbols suffice to absorb the enumeration bound
into a quadratic polynomial in the number of generated candidates. -/
theorem generated_cost_polynomial (alphabet : Records) (b d : ℕ)
    (hA : 2 ≤ alphabet.length) (ha : ∀ x ∈ alphabet, x.length ≤ b) :
    TupleProgram.powerCost alphabet d [[]] ≤
      400 * (d + 1) * alphabet.length ^ 2 * (alphabet.length ^ d) ^ 2 *
        ((d + 1) * b + 1) := by
  have h := powerCost_bound alphabet [[]] b 0 d ha (by simp)
  have hb : alphabet.length + 1 ≤ alphabet.length ^ 2 := by nlinarith
  have hp := Nat.pow_le_pow_left hb (d + 1)
  have he : (alphabet.length ^ 2) ^ (d + 1) =
      alphabet.length ^ 2 * (alphabet.length ^ d) ^ 2 := by
    rw [pow_succ]
    have he : (alphabet.length ^ 2) ^ d = (alphabet.length ^ d) ^ 2 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 d]
    rw [he]
    ring
  rw [he] at hp
  calc
    _ ≤ 400 * (d + 1) * (alphabet.length + 1) ^ (d + 1) * ((d + 1) * b + 1) := by
      norm_num only [List.length_cons, List.length_nil] at h
      nlinarith only [h]
    _ ≤ 400 * (d + 1) * (alphabet.length ^ 2 * (alphabet.length ^ d) ^ 2) *
        ((d + 1) * b + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
    _ = _ := by ring

theorem candidateEncoding_length_le (payloads : Records) (C : ℕ)
    (h : ∀ x ∈ payloads, x.length ≤ C) :
    (candidateEncoding payloads).length ≤ 1 + (2 * C + 2) * payloads.length := by
  have he : candidateEncoding payloads = ProgramEncoding.encodeRecords (payloads.map List.reverse) := by
    have hh := candidateEncoding_reverse (payloads.map List.reverse)
    simpa using hh
  rw [he]
  have hw : ∀ x ∈ payloads.map List.reverse, x.length ≤ C := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    simpa using h a ha
  simpa using ProgramEncoding.encodeRecords_length_le (payloads.map List.reverse) C hw

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
