import OAI.Analysis.Fourier.Main
import OAI.Analysis.Fourier.Dispersion.MassiveStatements
import OAI.Geometry.Kakeya.Quadratic.DimensionMinimum
import OAI.Geometry.Kakeya.Quadratic.MatrixDimension
import OAI.Analysis.PDE.WaveEquation.Sobolev
import OAI.Analysis.Fourier.Dispersion.Statements
import OAI.Geometry.Nikodym.LpTransfer
import OAI.Geometry.Nikodym.Hausdorff
import OAI.MeasureTheory.Kakeya.Minkowski

open OAI.Analysis.Fourier.Wave

/-! Further consequences connected to the unconditional main theorem. -/

noncomputable section
open Set _root_.MeasureTheory Metric Module
namespace OAI.Analysis.Fourier.LocalSmoothing

/-- The bounded-set clause of the Kakeya dimension corollary: both
lower and upper Minkowski dimensions have the full ambient value. -/
theorem kakeya_minkowski {n : ℕ} (hn : 2 ≤ n) {F : Set (Space n)}
    (hF : OAI.MeasureTheory.Kakeya.IsKakeyaSet F) (hbounded : Bornology.IsBounded F) :
    OAI.MeasureTheory.Kakeya.lowerMinkowskiDimension F = n ∧
      OAI.MeasureTheory.Kakeya.upperMinkowskiDimension F = n :=
  OAI.MeasureTheory.Kakeya.kakeya_implies_minkowski_dimensions
    OAI.MeasureTheory.Kakeya.kakeya hn hF hbounded

/-- The Euclidean Nikodym maximal estimate, with every positive epsilon
loss, for all Lⁿ inputs. -/
theorem nikodym_maximal : OAI.Geometry.Nikodym.NikodymMaximalConjecture :=
  OAI.Geometry.Nikodym.kakeyaMaximal_implies_nikodymMaximal OAI.MeasureTheory.Kakeya.kakeya_maximal

/-- Positive-length Nikodym incidence through a positive-volume set of
points forces full Hausdorff dimension. -/
theorem nikodym_dimension : OAI.Geometry.Nikodym.NikodymDimensionConjecture :=
  OAI.Geometry.Nikodym.nikodymMaximal_implies_dimension nikodym_maximal

/-- The displacement/velocity Sobolev estimate, including the lossless
`p = 2` endpoint and the one-derivative shift for velocity data. -/
theorem wave_data_sobolev : OAI.Analysis.PDE.WaveEquation.WaveDataSobolevEstimate :=
  OAI.Analysis.PDE.WaveEquation.waveDataSobolevEstimate_of_localSmoothing euclidean_local_smoothing

theorem constant_elliptic_local_smoothing : OAI.Analysis.Fourier.Dispersion.ConstantEllipticLocalSmoothing :=
  OAI.Analysis.Fourier.Dispersion.constantEllipticLocalSmoothing_of_logarithmicRefinement logarithmic_refinement

theorem constant_elliptic_logarithmic_sobolev : OAI.Analysis.Fourier.Dispersion.ConstantEllipticLogarithmicSobolev :=
  OAI.Analysis.Fourier.Dispersion.constantEllipticLogarithmicSobolev_of_logarithmicRefinement logarithmic_refinement

theorem massive_local_smoothing : OAI.Analysis.Fourier.Dispersion.MassiveLocalSmoothing :=
  OAI.Analysis.Fourier.Dispersion.massiveLocalSmoothing_of_localSmoothing euclidean_local_smoothing

theorem massive_logarithmic_sobolev : OAI.Analysis.Fourier.Dispersion.MassiveLogarithmicSobolev :=
  OAI.Analysis.Fourier.Dispersion.massiveLogarithmicSobolev_of_logarithmicSobolev logarithmic_sobolev

/-- The quadratic-curve dimension formula, with an attaining compact set,
without a Kakeya or local-smoothing hypothesis. -/
theorem quadratic_curve_dimension_infimum_attained
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hn : 1 ≤ finrank ℝ E) (B : E →ₗ[ℝ] E) {τ : ℝ} (hτ : 0 < τ)
    {Y : Set E} (hYc : IsCompact Y) (hY : (0 : E) ∈ interior Y) :
    ∃ R : ℝ, 0 < R ∧ ∀ R' : ℝ, R ≤ R' →
      sInf (dimH '' {K : Set (E × ℝ) |
        OAI.Geometry.Kakeya.Quadratic.HasQuadraticCurves B τ Y (closedBall 0 R') K}) =
        (finrank ℝ E - (finrank ℝ B.range - finrank ℝ (B.comp B).range) + 1 : ℕ) ∧
      ∃ K : Set (E × ℝ), OAI.Geometry.Kakeya.Quadratic.HasQuadraticCurves B τ Y (closedBall 0 R') K ∧
        dimH K = (finrank ℝ E - (finrank ℝ B.range - finrank ℝ (B.comp B).range) + 1 : ℕ) :=
  OAI.Geometry.Kakeya.Quadratic.quadratic_dimension_infimum_attained
    OAI.MeasureTheory.Kakeya.kakeya hn B hτ hYc hY

theorem matrix_quadratic_curve_dimension_infimum_attained
    {n : ℕ} (hn : 3 ≤ n) (B : Matrix (Fin (n-1)) (Fin (n-1)) ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ R : ℝ, 0 < R ∧ ∀ R' : ℝ, R ≤ R' →
      sInf (dimH '' {K : Set (Space (n-1) × ℝ) |
        OAI.Geometry.Kakeya.Quadratic.HasQuadraticCurves B.toEuclideanLin τ
          (OAI.Geometry.Kakeya.Quadratic.directionCube (n-1)) (closedBall 0 R') K}) =
        (n-B.rank+(B*B).rank : ℕ) ∧
      ∃ K : Set (Space (n-1) × ℝ),
        OAI.Geometry.Kakeya.Quadratic.HasQuadraticCurves B.toEuclideanLin τ
          (OAI.Geometry.Kakeya.Quadratic.directionCube (n-1)) (closedBall 0 R') K ∧
        dimH K = (n-B.rank+(B*B).rank : ℕ) :=
  OAI.Geometry.Kakeya.Quadratic.matrix_quadratic_dimension_infimum_attained
    OAI.MeasureTheory.Kakeya.kakeya hn B hτ

end OAI.Analysis.Fourier.LocalSmoothing
