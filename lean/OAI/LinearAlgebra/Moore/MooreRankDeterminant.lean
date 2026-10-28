import OAI.LinearAlgebra.Moore.MooreRank
import OAI.LinearAlgebra.Moore.MooreRankSpectrum
import OAI.Analysis.PDE.Dirichlet.PositiveDeterminant

noncomputable section
open scoped Matrix ComplexOrder
namespace OAI.LinearAlgebra.Moore

/-- A rank-sensitive scalar-shift estimate for the signed Moore determinant.
The rank premise is the genuine quaternion factorization rank bound. -/
theorem mooreDet_add_scalar_le_of_rank {m r : ℕ} {M a : ℝ}
    (B : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (hB : (complexify B).PosSemidef)
    (hupper : (M • (1 : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ)
      - complexify B).PosSemidef)
    (hr : QuaternionRankLE r B) (hrm : r ≤ m) (hM : 0 ≤ M) (ha : 0 ≤ a) :
    mooreDet m (B + a • 1) ≤ (M + a) ^ r * a ^ (m - r) := by
  have hshift : (complexify (B + a • 1)).PosSemidef := by
    rw [complexify_add, complexify_real_smul, complexify_one]
    exact hB.add (Matrix.PosSemidef.one.smul ha)
  have hsq := OAI.Analysis.PDE.Dirichlet.mooreDet_sq_eq_complexify_det_of_posSemidef
    (B + a • 1) hshift
  have hbound := complex_det_add_scalar_le_of_rank (complexify B) hB hupper
    hr.complexify_rank_le (r := 2 * r) (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hrm)
    hM ha
  rw [complexify_add, complexify_real_smul, complexify_one] at hsq
  have hpow : (M + a) ^ (2 * r) * a ^ (Fintype.card (Fin m × Fin 2) - 2 * r) =
      ((M + a) ^ r * a ^ (m - r)) ^ 2 := by
    have he : Fintype.card (Fin m × Fin 2) - 2 * r = (m - r) * 2 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      omega
    rw [he, mul_pow, ← pow_mul, ← pow_mul]
    simp [Nat.mul_comm]
  rw [hpow, ← hsq] at hbound
  have hp : 0 ≤ (M + a) ^ r * a ^ (m - r) :=
    mul_nonneg (pow_nonneg (add_nonneg hM ha) _) (pow_nonneg ha _)
  nlinarith

/-- Rank below the quaternion matrix dimension forces the Moore determinant
of a positive-semidefinite matrix to vanish. -/
theorem mooreDet_eq_zero_of_rank_lt {m r : ℕ}
    (B : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (hB : (complexify B).PosSemidef) (hr : QuaternionRankLE r B) (hrm : r < m) :
    mooreDet m B = 0 := by
  have hdet : (complexify B).det = 0 := by
    by_contra hn
    have he := Matrix.rank_of_det_ne_zero hn
    have hb := hr.complexify_rank_le
    rw [he] at hb
    simp only [Fintype.card_prod, Fintype.card_fin] at hb
    omega
  have hs := OAI.Analysis.PDE.Dirichlet.mooreDet_sq_eq_complexify_det_of_posSemidef B hB
  rw [hdet, Complex.zero_re] at hs
  nlinarith [sq_nonneg (mooreDet m B)]

end OAI.LinearAlgebra.Moore
