import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableChartFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.ProjectiveTransportNaturality

/-! # Stable Projective Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableProjectiveTransport

noncomputable section

/-! Canonical projective transport on every affine test of an
actual stable chart intersection, with arbitrary coefficient-base
morphism and arbitrary coefficient change. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {C A : Type u} [CommRing C] [CommRing A]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable {f : Spec (.of C) ⟶ Spec (.of R)}

def rawStableIntersectionProjectiveIso
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k)) :
    Projective.ProjectivePresentations.affineProjectiveSpace C n ≅ Projective.ProjectivePresentations.affineProjectiveSpace C n :=
  Configuration.ProjectiveTransport.configurationProjectiveTransport
    (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) (x ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k))
    (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i k (.of C) (x ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k))
    (StableChartFrames.stablePolynomialIntersection_frameRelated R i j k x)

theorem rawStableIntersectionProjectiveIso_natural
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k))
    (φ : C →+* A) :
    (rawStableIntersectionProjectiveIso R i j k (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ ≫ x)).hom.left ≫
        Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n =
      Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n ≫ (rawStableIntersectionProjectiveIso R i j k x).hom.left := by
  have hj : Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of A)
      ((HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ ≫ x) ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k) =
        fun c t => φ (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C)
          (x ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k) c t) := by
    simpa only [Category.assoc] using StableChartFrames.stablePolynomialChartPointVectors_coefficient R i j
      (x ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k) φ
  have hk : Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i k (.of A)
      ((HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ ≫ x) ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k) =
        fun c t => φ (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i k (.of C)
          (x ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k) c t) := by
    simpa only [Category.assoc] using StableChartFrames.stablePolynomialChartPointVectors_coefficient R i k
      (x ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k) φ
  unfold rawStableIntersectionProjectiveIso
  simp only [hj, hk]
  exact Configuration.ProjectiveTransportNaturality.configurationProjectiveTransport_coefficient_natural φ _ _
    (StableChartFrames.stablePolynomialIntersection_frameRelated R i j k x)
    (fun t => ⟨j.frame t⟩) ⟨j.additional⟩
    (StableChartFrames.stablePolynomialChartPointVectors_hasFrame R i j (x ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableProjectiveTransport
