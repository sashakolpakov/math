import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

/-- An integer upper binary logarithm sufficient for every construction bound. -/
def logSize (m : ℕ) : ℕ := Nat.log 2 m + 1

theorem logSize_pos (m : ℕ) : 0 < logSize m := by simp [logSize]

theorem lt_two_pow_logSize (m : ℕ) : m < 2 ^ logSize m := by
  exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) m

def gapDenom (m B : ℕ) : ℕ := 200 * B * logSize m

def degreeBound (m B : ℕ) : ℕ := 8 * gapDenom m B ^ 2 * logSize m

def degree (m B : ℕ) : ℕ := min m (degreeBound m B)

def distanceDenom (m B : ℕ) : ℕ := 20000 * B ^ 2 * logSize m ^ 2

theorem gapDenom_pos (m : ℕ) {B : ℕ} (hB : 0 < B) : 0 < gapDenom m B := by
  have := logSize_pos m
  unfold gapDenom
  positivity

theorem degreeBound_pos (m : ℕ) {B : ℕ} (hB : 0 < B) : 0 < degreeBound m B := by
  have := gapDenom_pos m hB
  have := logSize_pos m
  unfold degreeBound
  positivity

theorem degree_pos {m B : ℕ} (hm : 0 < m) (hB : 0 < B) : 0 < degree m B := by
  exact lt_min hm (degreeBound_pos m hB)

theorem degree_le (m B : ℕ) : degree m B ≤ m := min_le_left _ _

theorem degree_le_bound (m B : ℕ) : degree m B ≤ degreeBound m B := min_le_right _ _

theorem degree_le_power (m B : ℕ) : degree m B ≤ 2 ^ logSize m :=
  (degree_le m B).trans (lt_two_pow_logSize m).le

theorem eight_mul_le_degreeBound (m : ℕ) {B : ℕ} (hB : 0 < B) :
    8 * B ≤ degreeBound m B := by
  have hL : 1 ≤ logSize m := logSize_pos m
  have hq : B ≤ gapDenom m B := by unfold gapDenom; nlinarith
  have hqpos := gapDenom_pos m hB
  have hsq : gapDenom m B ≤ gapDenom m B ^ 2 := by nlinarith
  unfold degreeBound
  nlinarith

theorem exists_dimension (m : ℕ) {D : ℕ} (hD : 0 < D) :
    ∃ r : ℕ, m ≤ D * 2 ^ r := by
  refine ⟨logSize m, ?_⟩
  have hm := lt_two_pow_logSize m
  nlinarith

/-- Total increasing search for the first power-of-two vertex count whose
edge count covers the requested columns. The zero-degree default is never
used by the nonempty construction. -/
def dimensionFor (m D : ℕ) : ℕ :=
  if hD : 0 < D then Nat.find (exists_dimension m hD) else 0

theorem dimensionFor_spec (m : ℕ) {D : ℕ} (hD : 0 < D) :
    m ≤ D * 2 ^ dimensionFor m D := by
  simp only [dimensionFor, dite_eq_left hD]
  exact Nat.find_spec (exists_dimension m hD)

theorem dimensionFor_le (m : ℕ) {D r : ℕ} (hD : 0 < D)
    (hr : m ≤ D * 2 ^ r) : dimensionFor m D ≤ r := by
  simp only [dimensionFor, dite_eq_left hD]
  exact Nat.find_min' (exists_dimension m hD) hr

theorem dimensionFor_min (m : ℕ) {D r : ℕ} (hD : 0 < D)
    (hr : r < dimensionFor m D) : D * 2 ^ r < m := by
  simp only [dimensionFor, dite_eq_left hD] at hr
  exact Nat.lt_of_not_ge (Nat.find_min (exists_dimension m hD) hr)

theorem dimensionFor_self {m : ℕ} (hm : 0 < m) : dimensionFor m m = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact dimensionFor_le m hm (by simp)

theorem dimensionFor_edge_upper {m D : ℕ} (hm : 0 < m) (hD : 0 < D) (hDm : D ≤ m) :
    D * 2 ^ dimensionFor m D < 2 * m := by
  cases hr : dimensionFor m D with
  | zero => simp only [pow_zero, mul_one]; omega
  | succ r =>
    have hprev : D * 2 ^ r < m := dimensionFor_min m hD (by omega)
    simp only [pow_succ]
    nlinarith

theorem dimensionFor_lt_logSize (m : ℕ) {D : ℕ} (hD : 2 ≤ D) :
    dimensionFor m D < logSize m := by
  have hm := lt_two_pow_logSize m
  have hw : m ≤ D * 2 ^ (Nat.log 2 m) := by
    unfold logSize at hm
    rw [pow_succ] at hm
    nlinarith
  have hd := dimensionFor_le m (by omega : 0 < D) hw
  unfold logSize
  omega

def dimension (m B : ℕ) : ℕ := dimensionFor m (degree m B)

theorem dimension_lt_logSize {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    dimension m B < logSize m := by
  by_cases h : degreeBound m B ≤ m
  · have hD : 2 ≤ degreeBound m B := by
      have := eight_mul_le_degreeBound m hB
      omega
    simpa [dimension, degree, min_eq_right h] using dimensionFor_lt_logSize m hD
  · have hd : degree m B = m := min_eq_left (by omega)
    simpa [dimension, hd, dimensionFor_self hm] using logSize_pos m

theorem graph_edge_lower {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    m ≤ 2 ^ dimension m B * degree m B := by
  simpa [dimension, Nat.mul_comm] using dimensionFor_spec m (degree_pos hm hB)

theorem graph_edge_upper {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    2 ^ dimension m B * degree m B < 2 * m := by
  simpa [dimension, Nat.mul_comm] using
    dimensionFor_edge_upper hm (degree_pos hm hB) (degree_le m B)

theorem dimension_zero_of_small {m B : ℕ} (hm : 0 < m)
    (h : m ≤ degreeBound m B) : dimension m B = 0 := by
  simp [dimension, degree, min_eq_left h, dimensionFor_self hm]

theorem walsh_degree_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hr : dimension m B ≠ 0) :
    8 * gapDenom m B ^ 2 * (dimension m B + 1) ≤ degree m B := by
  have hlarge : degreeBound m B ≤ m := by
    by_contra h
    exact hr (dimension_zero_of_small hm (by omega))
  have hrL : dimension m B + 1 ≤ logSize m := dimension_lt_logSize hm hB
  rw [degree, min_eq_right hlarge, degreeBound]
  exact Nat.mul_le_mul_left _ hrL

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
