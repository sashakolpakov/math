import OAI.Geometry.Kakeya.Quadratic.DimensionMinimum
import Mathlib.LinearAlgebra.Matrix.Rank

open OAI.Analysis.Fourier.Wave

open Set _root_.MeasureTheory Metric Module
open scoped Topology ENNReal Matrix

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

/-- The usual closed coordinate cube, in Euclidean space. -/
def directionCube (m : ℕ) : Set (Space m) :=
  (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)) ⁻¹'
    Set.pi univ (fun _ => Icc (-1 : ℝ) 1)

theorem mem_directionCube {m : ℕ} (y : Space m) :
    y ∈ directionCube m ↔ ∀ i, -1 ≤ y i ∧ y i ≤ 1 := by
  simp [directionCube, Pi.le_def, forall_and]

theorem isCompact_directionCube (m : ℕ) : IsCompact (directionCube m) := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toContinuousLinearEquiv
  exact e.toHomeomorph.isCompact_preimage.mpr (isCompact_univ_pi fun _ => isCompact_Icc)

theorem zero_mem_interior_directionCube (m : ℕ) : (0 : Space m) ∈ interior (directionCube m) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (ball_mem_nhds (0 : Space m) zero_lt_one)
  intro y hy
  apply (mem_directionCube y).mpr
  intro i
  have hnorm : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
  have hi0 : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
  have hi : |y i| ≤ 1 := hi0.trans hnorm.le
  exact abs_le.mp hi

theorem finrank_matrix_range {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) :
    finrank ℝ B.toEuclideanLin.range = B.rank := by
  exact (B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis).symm

theorem finrank_matrix_square_range {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) :
    finrank ℝ (B.toEuclideanLin.comp B.toEuclideanLin).range = (B * B).rank := by
  rw [← Matrix.toLpLin_mul_same]
  exact finrank_matrix_range (B * B)

/-- Literal matrix version of the sharp quadratic-curve dimension
formula.  The infimum is attained, with the directions in [-1,1]^(n-1)
and the translations in any sufficiently large Euclidean closed ball.
In fact any positive finite curve-parameter length is allowed. -/
theorem matrix_quadratic_dimension_infimum_attained
    (hK : OAI.MeasureTheory.Kakeya.KakeyaConjecture) {n : ℕ} (hn : 3 ≤ n)
    (B : Matrix (Fin (n-1)) (Fin (n-1)) ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∃ R : ℝ, 0 < R ∧ ∀ R' : ℝ, R ≤ R' →
      sInf (dimH '' {K : Set (Space (n-1) × ℝ) |
        HasQuadraticCurves B.toEuclideanLin τ (directionCube (n-1)) (closedBall 0 R') K}) =
        (n - B.rank + (B * B).rank : ℕ) ∧
      ∃ K : Set (Space (n-1) × ℝ),
        HasQuadraticCurves B.toEuclideanLin τ (directionCube (n-1)) (closedBall 0 R') K ∧
        dimH K = (n - B.rank + (B * B).rank : ℕ) := by
  have hd : finrank ℝ (Space (n-1)) = n-1 := by simp [Space]
  have hdim : 1 ≤ finrank ℝ (Space (n-1)) := by rw [hd]; omega
  have hrank : B.rank ≤ n-1 := B.rank_le_width
  have hrank2 : (B * B).rank ≤ B.rank := Matrix.rank_mul_le_left B B
  have harith : n-1 - (B.rank - (B * B).rank) + 1 = n-B.rank+(B*B).rank := by omega
  simpa only [hd, finrank_matrix_range, finrank_matrix_square_range, harith] using
    quadratic_dimension_infimum_attained hK hdim B.toEuclideanLin hτ
      (isCompact_directionCube (n-1)) (zero_mem_interior_directionCube (n-1))

end OAI.Geometry.Kakeya.Quadratic
