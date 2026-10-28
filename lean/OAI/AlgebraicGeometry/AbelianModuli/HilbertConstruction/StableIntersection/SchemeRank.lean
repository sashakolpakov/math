import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.PolynomialRank
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialRankStalkPoints

/-! # Scheme Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.SchemeRank

noncomputable section

/-! The polynomial rank conditions from two stable charts agree on
their actual intersection on every scheme-valued test, by their
explicit normalized configurations at each stalk. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m)
variable (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)

def stableChartIntersectionLeftOver :
    Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k) ⟶
      Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j :=
  (algSpec (.of R)).map (CommAlgCat.ofHom
    (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced)).op

def stableChartIntersectionRightOver :
    Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k) ⟶
      Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i k :=
  (algSpec (.of R)).map (CommAlgCat.ofHom
    (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced)).op

variable (T : Over (Spec (.of R)))
variable (x : T ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k))

abbrev stableChartPointStalkMap_intersection_left (t : T.left) :=
  HilbertScheme.Presentations.Relative.AffineStalkPoints.relativeAffinePointStalkMap_postcomp (.of R) T
    (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced)
    (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced) x t

abbrev stableChartPointStalkMap_intersection_right (t : T.left) :=
  HilbertScheme.Presentations.Relative.AffineStalkPoints.relativeAffinePointStalkMap_postcomp (.of R) T
    (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i k.exponent k.balanced)
    (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced) x t

theorem stableIntersectionPolynomialRank_left_iff (D q : ℕ) :
    HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ULift.{u} (Fin q)) (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
      (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i j D) (x ≫ stableChartIntersectionLeftOver R i j k) ↔
    HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ULift.{u} (Fin q)) (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k))
      (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i (j.intersection k) D) x := by
  rw [Stable.PolynomialRankStalkPoints.stablePolynomialRank_stalk_iff, Stable.PolynomialRankStalkPoints.stablePolynomialRank_stalk_iff]
  apply forall_congr'
  intro t
  let := Stable.PolynomialRankStalkPoints.relativeTestStalkAlgebra R T t
  simp only [Stable.PolynomialRankStalkPoints.stableChartPointStalkMap, stableChartIntersectionLeftOver]
  rw [stableChartPointStalkMap_intersection_left]
  exact (PolynomialRank.stableChartIntersection_polynomialRank_comparisons R i j k
    (Stable.PolynomialRankStalkPoints.stableChartPointStalkMap R i (j.intersection k) T x t) D q).1

theorem stableIntersectionPolynomialRank_right_iff (D q : ℕ) :
    HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ULift.{u} (Fin q)) (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i k)
      (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i k D) (x ≫ stableChartIntersectionRightOver R i j k) ↔
    HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ULift.{u} (Fin q)) (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k))
      (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i (j.intersection k) D) x := by
  rw [Stable.PolynomialRankStalkPoints.stablePolynomialRank_stalk_iff, Stable.PolynomialRankStalkPoints.stablePolynomialRank_stalk_iff]
  apply forall_congr'
  intro t
  let := Stable.PolynomialRankStalkPoints.relativeTestStalkAlgebra R T t
  simp only [Stable.PolynomialRankStalkPoints.stableChartPointStalkMap, stableChartIntersectionRightOver]
  rw [stableChartPointStalkMap_intersection_right]
  exact (PolynomialRank.stableChartIntersection_polynomialRank_comparisons R i j k
    (Stable.PolynomialRankStalkPoints.stableChartPointStalkMap R i (j.intersection k) T x t) D q).2

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.SchemeRank
