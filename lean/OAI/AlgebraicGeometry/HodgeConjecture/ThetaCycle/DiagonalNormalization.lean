import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DiagonalFrame
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Diagonal Normalization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DiagonalNormalization.CM

noncomputable section

/-! ThetaCycle: explicit invertible diagonal bases normalize nondegenerate real
and imaginary diagonal forms to their actual signs. -/

open scoped Classical

def diagonalNormalizationScale (r : ℝ) : ℝ := (Real.sqrt |r|)⁻¹

theorem diagonal_normalization_scale_ne_zero (r : ℝ) (hr : r ≠ 0) :
    diagonalNormalizationScale r ≠ 0 :=
  inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (abs_pos.mpr hr)))

theorem diagonal_normalization_scalar (r : ℝ) (hr : r ≠ 0) :
    diagonalNormalizationScale r * r * diagonalNormalizationScale r = if 0 < r then 1 else -1 := by
  have hs : (Real.sqrt |r|) ^ 2 = |r| := Real.sq_sqrt (abs_nonneg r)
  have hn : Real.sqrt |r| ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (abs_pos.mpr hr))
  have he : diagonalNormalizationScale r * r * diagonalNormalizationScale r = r / |r| := by
    rw [← hs]
    unfold diagonalNormalizationScale
    field_simp
  rw [he]
  split_ifs with hp
  · rw [abs_of_pos hp, div_self hr]
  · have hneg : r < 0 := lt_of_le_of_ne (le_of_not_gt hp) hr
    rw [abs_of_neg hneg, div_neg, div_self hr]

variable {I : Type*} [Fintype I] [DecidableEq I]

def complexDiagonalNormalizer (r : I → ℝ) (hr : ∀ i, r i ≠ 0) : (Matrix I I ℂ)ˣ :=
  DiagonalFrame.CM.diagonalMatrixUnit (fun i => Units.mk0 (diagonalNormalizationScale (r i) : ℂ)
    (Complex.ofReal_ne_zero.mpr (diagonal_normalization_scale_ne_zero (r i) (hr i))))

theorem complex_diagonal_normalizer_form (r : I → ℝ) (hr : ∀ i, r i ≠ 0) (c : ℂ) :
    (complexDiagonalNormalizer r hr).val.conjTranspose *
        Matrix.diagonal (fun i => (r i : ℂ) * c) * (complexDiagonalNormalizer r hr).val =
      Matrix.diagonal (fun i => (if 0 < r i then (1 : ℂ) else -1) * c) := by
  change (Matrix.diagonal (fun i => (diagonalNormalizationScale (r i) : ℂ))).conjTranspose *
      Matrix.diagonal (fun i => (r i : ℂ) * c) *
      Matrix.diagonal (fun i => (diagonalNormalizationScale (r i) : ℂ)) = _
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have h : (diagonalNormalizationScale (r i) : ℂ) * (r i : ℂ) *
      (diagonalNormalizationScale (r i) : ℂ) = if 0 < r i then 1 else -1 := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) (diagonal_normalization_scalar (r i) (hr i))
    split_ifs with hp
    · simpa only [ite_eq_left hp, Complex.ofReal_mul, Complex.ofReal_one] using hc
    · simpa only [ite_eq_right hp, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one] using hc
  change star (diagonalNormalizationScale (r i) : ℂ) * ((r i : ℂ) * c) *
    (diagonalNormalizationScale (r i) : ℂ) = _
  rw [show star (diagonalNormalizationScale (r i) : ℂ) =
    (diagonalNormalizationScale (r i) : ℂ) from Complex.conj_ofReal _]
  calc
    _ = ((diagonalNormalizationScale (r i) : ℂ) * (r i : ℂ) *
        (diagonalNormalizationScale (r i) : ℂ)) * c := by ring
    _ = _ := by rw [h]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DiagonalNormalization.CM
