import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedFrameIndex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartProjectivePoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.MonomialMatrix
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.QuasiCompact
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankAffineCriterion

/-! # Configuration Polynomial Rank Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ConfigurationPolynomialRankLocus

noncomputable section

/-! On each stable balanced configuration chart, the actual monomial
evaluation matrix defines a quasi-compact locally closed rank locus.
Its universal property tests flatness and rank of the cokernel on all
scheme stalks; it includes the actual pivot residual equations. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.QuasiCompact.Grassmannian
universe u
variable (R : Type u) [CommRing R] {n m : ℕ}
variable (i : Fin m) (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)

def stableConfigurationPolynomialRankAmbient : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap R (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))))

def stableConfigurationPolynomialMatrix (D : ℕ) :
    Matrix (ULift.{u} (Fin m)) (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n D)
      Γ((stableConfigurationPolynomialRankAmbient R i j).left, ⊤) :=
  (Configuration.MonomialMatrix.configurationMonomialMatrix (fun c : ULift.{u} (Fin m) =>
    Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate j.exponent j.complement
      j.balanced j.complete c.down) D).map
    (Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv.hom

def stableConfigurationPolynomialRankLocus (D k : ℕ) : Over (Spec (.of R)) :=
  HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ULift.{u} (Fin k)) (stableConfigurationPolynomialRankAmbient R i j)
    (stableConfigurationPolynomialMatrix R i j D)

def stableConfigurationPolynomialRankInclusion (D k : ℕ) :
    stableConfigurationPolynomialRankLocus R i j D k ⟶ stableConfigurationPolynomialRankAmbient R i j :=
  HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ULift.{u} (Fin k)) (stableConfigurationPolynomialRankAmbient R i j)
    (stableConfigurationPolynomialMatrix R i j D)

instance stableConfigurationPolynomialRankInclusion_isImmersion (D k : ℕ) :
    IsImmersion (stableConfigurationPolynomialRankInclusion R i j D k).left :=
  HilbertScheme.Presentations.MatrixRank.Immersion.Grassmannian.matrixRankParameterMap_isImmersion _ _

instance stableConfigurationPolynomialRankInclusion_quasiCompact (D k : ℕ) :
    QuasiCompact (stableConfigurationPolynomialRankInclusion R i j D k).left :=
  HilbertScheme.Presentations.MatrixRank.QuasiCompact.Grassmannian.matrixRankParameterMap_quasiCompact _ _

theorem stableConfigurationPolynomialRankLocus_point_iff (D k : ℕ)
    (T : Over (Spec (.of R))) (x : T ⟶ stableConfigurationPolynomialRankAmbient R i j) :
    HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ULift.{u} (Fin k)) (stableConfigurationPolynomialRankAmbient R i j)
      (stableConfigurationPolynomialMatrix R i j D) x ↔
      ∃! y : T ⟶ stableConfigurationPolynomialRankLocus R i j D k,
        y ≫ stableConfigurationPolynomialRankInclusion R i j D k = x :=
  HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.matrixCokernelFlatRank_iff_unique_lift _ _ x

theorem stableConfigurationPolynomialRankLocus_affine_iff (D k : ℕ)
    (A : CommRingCat.{u}) {f : Spec A ⟶ Spec (.of R)}
    (x : Over.mk f ⟶ stableConfigurationPolynomialRankAmbient R i j) :
    (∃! y : Over.mk f ⟶ stableConfigurationPolynomialRankLocus R i j D k,
      y ≫ stableConfigurationPolynomialRankInclusion R i j D k = x) ↔
    (Module.Flat A ((ULift.{u} (Fin m) → A) ⧸
      (Matrix.toLin' (HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients (stableConfigurationPolynomialRankAmbient R i j)
        (stableConfigurationPolynomialMatrix R i j D) A x)).range) ∧
      ∀ p : PrimeSpectrum A, Module.rankAtStalk (R := A)
        ((ULift.{u} (Fin m) → A) ⧸
          (Matrix.toLin' (HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients (stableConfigurationPolynomialRankAmbient R i j)
            (stableConfigurationPolynomialMatrix R i j D) A x)).range) p + k = m) := by
  rw [← stableConfigurationPolynomialRankLocus_point_iff]
  simpa only [Fintype.card_ulift, Fintype.card_fin] using
    (HilbertConstruction.Matrix.RankAffineCriterion.matrixRank_affine_iff (ι := ULift.{u} (Fin k)) (stableConfigurationPolynomialRankAmbient R i j)
      (stableConfigurationPolynomialMatrix R i j D) A x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ConfigurationPolynomialRankLocus
