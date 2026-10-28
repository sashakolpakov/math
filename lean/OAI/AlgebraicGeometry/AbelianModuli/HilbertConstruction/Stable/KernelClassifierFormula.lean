import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankClassifierCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialMatrixCoefficients

/-! # Kernel Classifier Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.KernelClassifierFormula

noncomputable section

/-! A lift to a stable configuration rank locus is classified by the
kernel of the literal monomial matrix of its normalized chart vectors. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m)
variable (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D k : ℕ)
variable (C : CommRingCat.{u}) {f : Spec C ⟶ Spec (.of R)}
variable (x : Over.mk f ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
variable (y : Over.mk f ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D k)
variable (hy : y ≫ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D k = x)

include hy in
theorem stablePolynomialKernelClassifier_affine_of_kernel
    (Q : Module.Grassmannian C (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n D → C) (Fintype.card (ULift.{u} (Fin k))))
    (hQ : Q.toSubmodule =
      (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix (PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x) D)).ker) :
    y ≫ HilbertConstruction.Matrix.RankKernelClassifier.stableConfigurationPolynomialKernelClassifier R i j D k = HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f Q := by
  have hc : SchemeFlatMatrixGrassmannian.affineSchemeMatrixCoefficients (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i j D) C
      (y.left ≫ (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D k).left) =
        Configuration.MonomialMatrix.configurationMonomialMatrix (PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x) D := by
    rw [show y.left ≫ (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D k).left = x.left from
      congrArg Over.Hom.left hy]
    exact PolynomialMatrixCoefficients.stableConfigurationPolynomialMatrix_coefficients R i j C x D
  have h := HilbertConstruction.Matrix.RankClassifierCoefficients.matrixRankKernelClassifier_affine_of_kernel (ι := ULift.{u} (Fin k))
    (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i j D)
    C y.left Q (by
      change Q.toSubmodule = (Matrix.toLin'
        (SchemeFlatMatrixGrassmannian.affineSchemeMatrixCoefficients (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
          (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i j D) C
          (y.left ≫ (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D k).left))).ker
      rw [hc]
      exact hQ)
  apply Over.OverMorphism.ext
  have hyw : y.left ≫ (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ULift.{u} (Fin k))
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i j D)).hom = f := y.w
  rw [hyw] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.KernelClassifierFormula
