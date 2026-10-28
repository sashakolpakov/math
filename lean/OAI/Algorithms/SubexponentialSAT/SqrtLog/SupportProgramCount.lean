import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramEnumeration
import OAI.Algorithms.SubexponentialSAT.ProgramEncoding

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SupportProgram

open scoped BigOperators

def count (n J : ℕ) : ℕ := ∑ j ∈ Finset.range J, n.choose j

@[simp] theorem count_zero (n : ℕ) : count n 0 = 0 := by simp [count]

@[simp] theorem count_succ (n J : ℕ) :
    count n (J + 1) = count n J + n.choose J := by
  simp [count, Finset.sum_range_succ]

theorem count_pascal (n J : ℕ) :
    count (n + 1) (J + 1) = count n (J + 1) + count n J := by
  induction J with
  | zero => simp [count]
  | succ J ih =>
      rw [count_succ (n + 1) (J + 1), ih, Nat.choose_succ_succ,
        count_succ n (J + 1), count_succ n J]
      simp only [Nat.succ_eq_add_one]
      omega

@[simp] theorem count_empty_variables (J : ℕ) : count 0 (J + 1) = 1 := by
  induction J with
  | zero => simp [count]
  | succ J ih => rw [count_succ, ih]; simp

@[simp] theorem masks_length (n J : ℕ) : (masks n J).length = count n J := by
  induction n generalizing J with
  | zero => cases J <;> simp only [masks, List.length_nil, List.length_cons, count_zero, count_empty_variables]
  | succ n ih =>
      cases J with
      | zero => simp [masks]
      | succ J => simp only [masks, List.length_append, List.length_map, ih, count_pascal]

theorem count_eq_supportUniverse (n J : ℕ) :
    count n J = (Squarefree.Sparse.supportUniverse (Finset.univ : Finset (Fin n)) J).card :=
  (Squarefree.Sparse.finite_support_count n J).symm

/-- Number of emitted payload bits, counted with their actual fixed mask width. -/
theorem masks_payload_size (n J : ℕ) :
    ((masks n J).map List.length).sum = n * count n J := by
  have hm : (masks n J).map List.length = (masks n J).map (fun _ => n) := by
    apply List.map_congr_left
    intro xs hx
    exact (mem_masks n J xs).mp hx |>.1
  rw [hm]
  simp [ List.sum_replicate, Nat.mul_comm]

/-- The concrete self-delimiting output requires only O(n M_J) bits. -/
theorem encoded_masks_length (n J : ℕ) :
    (Encoding.encodeList id (masks n J)).length = (2 * n + 2) * count n J + 1 := by
  change (ProgramEncoding.encodeRecords (masks n J)).length = _
  rw [ProgramEncoding.encodeRecords_length, masks_payload_size, masks_length]
  ring

theorem calls_le_count (n J : ℕ) (hJ : 0 < J) :
    calls n J ≤ (2 * n + 1) * count n J := by
  simpa only [masks_length] using calls_le n J hJ

end SubexponentialSAT.SqrtLog.SupportProgram

end OAI.Algorithms
