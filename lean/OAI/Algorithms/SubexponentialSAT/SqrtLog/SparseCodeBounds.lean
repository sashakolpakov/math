import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeParameters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

def localRows (m B : ℕ) : ℕ := degree m B / (8 * B) + 1

def totalRows (m B : ℕ) : ℕ := 2 * 2 ^ dimension m B * localRows m B

theorem localRows_lower {m B : ℕ} (hB : 0 < B) :
    degree m B ≤ 8 * B * localRows m B := by
  have hpos : 0 < 8 * B := by omega
  have hmod := Nat.mod_lt (degree m B) hpos
  have hdiv := Nat.mod_add_div (degree m B) (8 * B)
  unfold localRows
  nlinarith

theorem localRows_upper (m B : ℕ) :
    8 * B * localRows m B ≤ degree m B + 8 * B := by
  have hh := Nat.div_mul_le_self (degree m B) (8 * B)
  unfold localRows
  nlinarith

theorem totalRows_le {n m B : ℕ} (hn : 0 < n) (hm : 0 < m) (hB : 0 < B)
    (hmb : m ≤ n * B) : totalRows m B ≤ 3 * n := by
  by_cases hlarge : degreeBound m B ≤ m
  · have hd : degree m B = degreeBound m B := min_eq_right hlarge
    have hbudget : 4 * B * localRows m B ≤ degree m B := by
      have htop := localRows_upper m B
      have hbig := eight_mul_le_degreeBound m hB
      rw [← hd] at hbig
      nlinarith
    have hedge := graph_edge_upper hm hB
    have hrows : totalRows m B * (2 * B) < n * (2 * B) := by
      calc
        _ = 2 ^ dimension m B * (4 * B * localRows m B) := by
          unfold totalRows
          ring
        _ ≤ 2 ^ dimension m B * degree m B := Nat.mul_le_mul_left _ hbudget
        _ < 2 * m := hedge
        _ ≤ n * (2 * B) := by nlinarith
    have : totalRows m B < n := Nat.lt_of_mul_lt_mul_right hrows
    omega
  · have hd : degree m B = m := min_eq_left (by omega)
    have hr : dimension m B = 0 := dimension_zero_of_small hm (by omega)
    have htop := localRows_upper m B
    rw [hd] at htop
    have hh : (8 * localRows m B) * B ≤ (n + 8) * B := by nlinarith
    have hrows : 8 * localRows m B ≤ n + 8 :=
      le_of_mul_le_mul_right hh hB
    simp only [totalRows, hr, pow_zero, mul_one]
    omega

theorem relative_fraction (m : ℕ) {B : ℕ} (hB : 0 < B) :
    (1 / (100 * (B : ℝ) * logSize m)) *
        (1 / (100 * (B : ℝ) * logSize m) - 1 / (gapDenom m B : ℝ)) =
      1 / (distanceDenom m B : ℝ) := by
  have hbr : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hlr : (logSize m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (logSize_pos m)
  simp only [gapDenom, distanceDenom, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ; ring

theorem distanceDenom_pos (m : ℕ) {B : ℕ} (hB : 0 < B) :
    0 < distanceDenom m B := by
  have := logSize_pos m
  unfold distanceDenom
  positivity

theorem relativeDistance_integer {C R : Type*} [Fintype C]
    {Q : CheckMatrix R C} {P : ℕ} (hP : 0 < P)
    (hQ : HasRelativeDistance Q (1 / (P : ℝ)))
    (w : C → F3) (hw : IsCodeword Q w) (hw0 : w ≠ 0) :
    Fintype.card C ≤ P * weight w := by
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  have hh := hQ w hw hw0
  have hh' : (Fintype.card C : ℝ) / (P : ℝ) ≤ (weight w : ℝ) := by
    convert hh using 1 ; ring
  have hx := (div_le_iff₀ hp).mp hh'
  exact_mod_cast (show (Fintype.card C : ℝ) ≤ (P : ℝ) * (weight w : ℝ) by nlinarith)

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
