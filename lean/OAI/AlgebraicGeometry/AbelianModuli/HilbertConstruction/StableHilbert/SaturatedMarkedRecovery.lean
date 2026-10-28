import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.MarkedPointRecovery

/-! # Saturated Marked Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedMarkedRecovery.StableHilbertSaturatedRecovery

noncomputable section

/-! Marked homogeneous sections retain their prescribed projective coordinates
under the original saturated-family recovery isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Type u} [CommRing C] [IsNoetherianRing C] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    {f : Spec (.of C) ⟶ Spec (.of R)}
variable (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
    (hc : c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H = x)
    (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C n H)
    (hI : HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) c
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H) = I.nativeHilbertFamily f)
    {X : Over (Spec (.of C))} (e : X ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
    (p : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n)
    (he : (e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n = p.left)

include hc he in
theorem sourceIso_markedPoint (z : Fin m) (s : Spec (.of C) ⟶ X.left)
    (hp : (s ≫ e.hom.left) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of C) C
        (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) x ⟨z⟩)
        (j.coordinate z) (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i j (.of C) x ⟨z⟩)) :
    s ≫ (SaturatedRecovery.StableHilbertSaturatedRecovery.sourceIso R i j D H hH c I hI e).hom.left ≫
      ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H).baseChange
        (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).embedding.left =
          (PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z).left := by
  exact (congrArg (fun a => s ≫ a)
    (SaturatedRecovery.StableHilbertSaturatedRecovery.sourceIso_embedding_left R i j D H hH c I hI e p he)).trans
      (MarkedPointRecovery.stableHilbertPrescribedPoint_from_homogeneous R i j D H c x hc I
        e.hom.left p.left he z s hp)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedMarkedRecovery.StableHilbertSaturatedRecovery
