import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCodeWeight

namespace OAI.Algorithms

/-! The reviewed log-size variant of the local code, using only integer bounds. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open SparseCode

theorem local_exponent_lt (D B ell t : ℕ) (hB : 0 < B) (hell : 0 < ell)
    (ht : D ≤ 8 * B * t) (hh : 0 < D / (100 * B * ell)) :
    3 * ell * (D / (100 * B * ell)) < t := by
  have hdiv := Nat.div_mul_le_self D (100 * B * ell)
  have hprod : B * (100 * ell * (D / (100 * B * ell))) ≤ B * (8 * t) := by
    nlinarith
  have hcancel := Nat.le_of_mul_le_mul_left hprod hB
  have hpositive := Nat.mul_pos hell hh
  nlinarith

theorem four_mul_le_log_power (D ell : ℕ) (hell : 0 < ell)
    (hD : D ≤ 2 ^ ell) : 4 * D ≤ 2 ^ (3 * ell) := by
  calc
    4 * D ≤ 4 * 2 ^ ell := Nat.mul_le_mul_left _ hD
    _ = 2 ^ (ell + 2) := by simp [pow_add, Nat.mul_comm]
    _ ≤ 2 ^ (3 * ell) := Nat.pow_le_pow_right (by decide) (by omega)

/-- An unconditional finite local-code existence theorem. `ell` only needs
to bound the binary logarithm of the local length; no entropy estimate is
assumed. The row budget is expressed without rounded division. -/
theorem exists_local_code_log_bound (D B ell t : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hD : D ≤ 2 ^ ell)
    (ht : D ≤ 8 * B * t) :
    ∃ Q : CheckMatrix (Fin t) (Fin D),
      HasDistance Q (D / (100 * B * ell) + 1) := by
  classical
  apply exists_distance_of_card
  by_cases hh : D / (100 * B * ell) = 0
  · have he : (Finset.univ.filter fun v : Fin D → F3 =>
        v ≠ 0 ∧ weight v < D / (100 * B * ell) + 1) = ∅ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp
      intro hv
      have hp := (weight_pos_iff v).mpr hv
      omega
    rw [he, Finset.card_empty]
    positivity
  · have hhpos : 0 < D / (100 * B * ell) := Nat.pos_of_ne_zero hh
    have hDpos : 0 < D := by
      by_contra hn
      have : D = 0 := by omega
      simp [this] at hh
    have hsubset : (Finset.univ.filter fun v : Fin D → F3 =>
        v ≠ 0 ∧ weight v < D / (100 * B * ell) + 1) ⊆
        lowWords D (D / (100 * B * ell)) := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact (mem_lowWords v).mpr (Nat.lt_succ_iff.mp hv.2)
    calc
      (Finset.univ.filter fun v : Fin D → F3 =>
          v ≠ 0 ∧ weight v < D / (100 * B * ell) + 1).card
          ≤ (lowWords D (D / (100 * B * ell))).card := Finset.card_le_card hsubset
      _ ≤ (4 * D) ^ (D / (100 * B * ell)) := lowWords_card_le_four _ _ hDpos
      _ ≤ (2 ^ (3 * ell)) ^ (D / (100 * B * ell)) :=
        Nat.pow_le_pow_left (four_mul_le_log_power D ell hell hD) _
      _ = 2 ^ (3 * ell * (D / (100 * B * ell))) := (pow_mul _ _ _).symm
      _ < 2 ^ t := Nat.pow_lt_pow_right (by decide)
        (local_exponent_lt D B ell t hB hell ht hhpos)
      _ ≤ 3 ^ t := Nat.pow_le_pow_left (by decide) _

theorem relative_of_log_distance {D B ell t : ℕ}
    (hB : 0 < B) (hell : 0 < ell)
    (Q : CheckMatrix (Fin t) (Fin D))
    (hQ : HasDistance Q (D / (100 * B * ell) + 1)) :
    HasRelativeDistance Q (1 / (100 * (B : ℝ) * (ell : ℝ))) := by
  intro v hv hv0
  have hd : 0 < 100 * B * ell := by positivity
  have hbound := Nat.lt_mul_div_succ D hd
  have hboundR : (D : ℝ) <
      (100 * (B : ℝ) * (ell : ℝ)) * ((D / (100 * B * ell) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hbound
  have hdR : 0 < 100 * (B : ℝ) * (ell : ℝ) := by positivity
  have hw := hQ v hv hv0
  simp only [Fintype.card_fin]
  calc
    1 / (100 * (B : ℝ) * (ell : ℝ)) * D =
        (D : ℝ) / (100 * (B : ℝ) * (ell : ℝ)) := by ring
    _ ≤ ((D / (100 * B * ell) + 1 : ℕ) : ℝ) :=
      (div_le_iff₀ hdR).mpr (by simpa only [mul_comm] using hboundR.le)
    _ ≤ (weight v : ℝ) := by exact_mod_cast hw

theorem exists_local_relative_code_log_bound (D B ell t : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hD : D ≤ 2 ^ ell)
    (ht : D ≤ 8 * B * t) :
    ∃ Q : CheckMatrix (Fin t) (Fin D),
      HasRelativeDistance Q (1 / (100 * (B : ℝ) * (ell : ℝ))) := by
  obtain ⟨Q, hQ⟩ := exists_local_code_log_bound D B ell t hB hell hD ht
  exact ⟨Q, relative_of_log_distance hB hell Q hQ⟩

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
