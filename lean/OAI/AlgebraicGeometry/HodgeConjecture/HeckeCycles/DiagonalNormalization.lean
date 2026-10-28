import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Diagonal Normalization -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalNormalization.CM

/-! Actual invertible diagonal bases normalize real or imaginary
diagonal forms to their signs. -/

open scoped Classical

def scale (r : ℝ) : ℝ := (Real.sqrt |r|)⁻¹

theorem scale_ne_zero (r : ℝ) (hr : r ≠ 0) : scale r ≠ 0 :=
  inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (abs_pos.mpr hr)))

theorem scalar (r : ℝ) (hr : r ≠ 0) : scale r * r * scale r = if 0 < r then 1 else -1 := by
  have hs : (Real.sqrt |r|) ^ 2 = |r| := Real.sq_sqrt (abs_nonneg r)
  have hn : Real.sqrt |r| ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (abs_pos.mpr hr))
  have he : scale r * r * scale r = r / |r| := by
    rw [← hs]
    unfold scale
    field_simp
  rw [he]
  split_ifs with hp
  · rw [abs_of_pos hp, div_self hr]
  · have hneg : r < 0 := lt_of_le_of_ne (le_of_not_gt hp) hr
    rw [abs_of_neg hneg, div_neg, div_self hr]

variable {I : Type*} [Fintype I] [DecidableEq I]

def normalizer (r : I → ℝ) (hr : ∀ i, r i ≠ 0) : (Matrix I I ℂ)ˣ :=
  Source.QuadraticForms.CM.diagonalUnit (fun i => Units.mk0 (scale (r i) : ℂ)
    (Complex.ofReal_ne_zero.mpr (scale_ne_zero (r i) (hr i))))

theorem form (r : I → ℝ) (hr : ∀ i, r i ≠ 0) (c : ℂ) :
    (normalizer r hr).val.conjTranspose * Matrix.diagonal (fun i => (r i : ℂ) * c) *
      (normalizer r hr).val = Matrix.diagonal (fun i => (if 0 < r i then (1 : ℂ) else -1) * c) := by
  change (Matrix.diagonal (fun i => (scale (r i) : ℂ))).conjTranspose *
      Matrix.diagonal (fun i => (r i : ℂ) * c) *
      Matrix.diagonal (fun i => (scale (r i) : ℂ)) = _
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have h : (scale (r i) : ℂ) * (r i : ℂ) * (scale (r i) : ℂ) =
      if 0 < r i then 1 else -1 := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) (scalar (r i) (hr i))
    split_ifs with hp
    · simpa only [ite_eq_left hp, Complex.ofReal_mul, Complex.ofReal_one] using hc
    · simpa only [ite_eq_right hp, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one] using hc
  change star (scale (r i) : ℂ) * ((r i : ℂ) * c) * (scale (r i) : ℂ) = _
  rw [show star (scale (r i) : ℂ) = (scale (r i) : ℂ) from Complex.conj_ofReal _]
  calc
    _ = ((scale (r i) : ℂ) * (r i : ℂ) * (scale (r i) : ℂ)) * c := by ring
    _ = _ := by rw [h]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalNormalization.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalNormalization.CM.Values

/-! Explicit inverse coordinates of the actual orthonormal bases. -/

open scoped Classical _root_.Matrix Kronecker

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem inverse (r : I → ℝ) (hr : ∀ i, r i ≠ 0) :
    (normalizer r hr).inv =
      Matrix.diagonal (fun i => (Real.sqrt |r i| : ℂ)) := by
  change Matrix.diagonal (fun i => (scale (r i) : ℂ)⁻¹) = _
  simp only [scale, Complex.ofReal_inv, inv_inv]

theorem tensor (r : I → ℝ) (s : J → ℝ)
    (hr : ∀ i, r i ≠ 0) (hs : ∀ j, s j ≠ 0) :
    (normalizer r hr).inv ⊗ₖ
      (normalizer s hs).inv =
        Matrix.diagonal (fun ij => ((Real.sqrt |r ij.1| * Real.sqrt |s ij.2| : ℝ) : ℂ)) := by
  rw [inverse, inverse, Matrix.diagonal_kronecker_diagonal]
  simp only [Complex.ofReal_mul]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalNormalization.CM.Values

end

end OAI
