import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ConfigurationPolynomialRankLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ChartNormalizedRankPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MatrixRankComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.CokernelRelabeling
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineStalkPoints

/-! # Polynomial Rank Stalk Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialRankStalkPoints

noncomputable section

/-! The scheme-theoretic polynomial rank condition on a stable chart
is exactly the polynomial flat-rank condition on its actual normalized
configuration in every stalk of every test scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineStalkPoints
universe u
variable (R : Type u) [CommRing R]

@[instance_reducible]
def relativeTestStalkAlgebra (T : Over (Spec (.of R))) (t : T.left) : Algebra R (T.left.presheaf.stalk t) :=
  HilbertScheme.Presentations.Relative.AffineStalkPoints.relativeStalkAlgebra (.of R) T t

variable {n m : ℕ} (i : Fin m) (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (T : Over (Spec (.of R))) (x : T ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)

def stableChartPointStalkMap (t : T.left) :
    letI := relativeTestStalkAlgebra R T t
    Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →ₐ[R] T.left.presheaf.stalk t := by
  letI := relativeTestStalkAlgebra R T t
  exact HilbertScheme.Presentations.Relative.AffineStalkPoints.relativeAffinePointStalkMap (.of R) T
    (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced) x t

theorem stablePolynomialMatrix_stalk (D : ℕ) (t : T.left) :
    let := relativeTestStalkAlgebra R T t
    HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.matrixAtStalk (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i j D) x t =
      Configuration.MonomialMatrix.configurationMonomialMatrix
        (fun c : ULift.{u} (Fin m) => ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
          (stableChartPointStalkMap R i j T x t) c.down) D := by
  let := relativeTestStalkAlgebra R T t
  have h := Configuration.MonomialMatrix.configurationMonomialMatrix_map
    (stableChartPointStalkMap R i j T x t).toRingHom
    (fun c : ULift.{u} (Fin m) => Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate
      j.exponent j.complement j.balanced j.complete c.down) (d := D)
  exact h

theorem stablePolynomialRank_stalk_iff (D k : ℕ) :
    HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ULift.{u} (Fin k)) (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i j D) x ↔
    ∀ t : T.left, letI := relativeTestStalkAlgebra R T t
      BalancedChart.PolynomialRankInvariance.ConfigurationPolynomialFlatRank
        (ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j (stableChartPointStalkMap R i j T x t)) D k := by
  apply forall_congr'
  intro t
  let := relativeTestStalkAlgebra R T t
  rw [stablePolynomialMatrix_stalk]
  simp only [Fintype.card_ulift, Fintype.card_fin]
  exact (Local.MatrixRankComparison.localMatrixCokernel_rankAtStalk_iff_finrank
    (Configuration.MonomialMatrix.configurationMonomialMatrix
      (fun c : ULift.{u} (Fin m) => ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
        (stableChartPointStalkMap R i j T x t) c.down) D) k m).symm.trans
      (Configuration.CokernelRelabeling.configurationMonomialMatrix_flatRank_relabel_iff
        (ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j (stableChartPointStalkMap R i j T x t)) D k m Equiv.ulift)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialRankStalkPoints
