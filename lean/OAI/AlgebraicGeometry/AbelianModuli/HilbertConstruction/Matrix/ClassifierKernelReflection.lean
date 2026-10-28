import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.QuotientPointInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.KernelClassifierFormula

/-! # Classifier Kernel Reflection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.ClassifierKernelReflection

noncomputable section

/-! The scheme matrix-kernel classifier both constructs and
reflects the exact affine kernel, rather than just its dimension. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι μ ν : Type u} [Fintype ι] [Fintype μ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]
variable {S : Scheme.{u}} (M : Over S) (F : Matrix ν μ Γ(M.left, ⊤))

theorem matrixRankKernelClassifier_affine_iff_kernel (C : CommRingCat.{u})
    {f : Spec C ⟶ S} (y : Over.mk f ⟶ HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F)
    (Q : Module.Grassmannian C (μ → C) (Fintype.card ι)) :
    y ≫ RankKernelClassifier.matrixRankKernelClassifier M F = HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f Q ↔
      Q.toSubmodule = (Matrix.toLin' (SchemeFlatMatrixGrassmannian.affineSchemeMatrixCoefficients M F C
        (y.left ≫ (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F).left))).ker := by
  let L := SchemeFlatMatrixGrassmannian.affineMatrixKernelPoint (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F)
    (F.map (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F).left.appTop.hom)
    (RankKernelClassifier.matrixRankPulledMatrix_flatRank M F) C y.left
  have hc : y ≫ RankKernelClassifier.matrixRankKernelClassifier M F = HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f L := by
    apply Over.OverMorphism.ext
    have h := RankKernelClassifier.matrixRankKernelClassifier_affine M F C y.left
    have hyw : y.left ≫ (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F).hom = f := y.w
    rw [hyw] at h
    exact h
  have hL : L.toSubmodule = (Matrix.toLin' (SchemeFlatMatrixGrassmannian.affineSchemeMatrixCoefficients M F C
      (y.left ≫ (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F).left))).ker := by
    change (Matrix.toLin' (SchemeFlatMatrixGrassmannian.affineSchemeMatrixCoefficients (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F)
      (F.map (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F).left.appTop.hom) C y.left)).ker = _
    rw [RankClassifierCoefficients.affineSchemeMatrixCoefficients_pullback]
  constructor
  · intro h
    have he : L = Q := Relative.QuotientPointInjectivity.relativeQuotientClassifyingPoint_injective f (hc.symm.trans h)
    exact he ▸ hL
  · intro h
    have he : L = Q := Module.Grassmannian.ext (hL.trans h.symm)
    exact he ▸ hc

theorem stablePolynomialKernelClassifier_affine_iff_kernel
    (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m)
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D k : ℕ)
    (C : CommRingCat.{u}) {f : Spec C ⟶ Spec (.of R)}
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
    (y : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D k)
    (hy : y ≫ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D k = x)
    (Q : Module.Grassmannian C (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n D → C) (Fintype.card (ULift.{u} (Fin k)))) :
    y ≫ RankKernelClassifier.stableConfigurationPolynomialKernelClassifier R i j D k = HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f Q ↔
      Q.toSubmodule = (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x) D)).ker := by
  change y ≫ RankKernelClassifier.matrixRankKernelClassifier _ _ = _ ↔ _
  rw [matrixRankKernelClassifier_affine_iff_kernel]
  change Q.toSubmodule = (Matrix.toLin' (SchemeFlatMatrixGrassmannian.affineSchemeMatrixCoefficients
    (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i j D) C
    (y.left ≫ (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D k).left))).ker ↔ _
  rw [show y.left ≫ (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D k).left = x.left from
    congrArg Over.Hom.left hy]
  have hc : SchemeFlatMatrixGrassmannian.affineSchemeMatrixCoefficients (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
      (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i j D) C x.left =
      Configuration.MonomialMatrix.configurationMonomialMatrix (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x) D :=
    Stable.PolynomialMatrixCoefficients.stableConfigurationPolynomialMatrix_coefficients R i j C x D
  rw [hc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.ClassifierKernelReflection
