import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TorsionConfigurationLift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedCoordinateRecovery

/-! # Torsion Configuration Family Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionConfigurationFamilyRecovery

noncomputable section

/-! The universal embedded projective family on the constructed
configuration Hilbert locus recovers the exact family of the original
saturated ideal at every noetherian high-torsion configuration. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (C : CommRingCat.{u}) [IsNoetherianRing C]
variable {g N n r : ℕ} {δ : Fin g → ℕ} [NeZero n] {P : Polynomial ℚ}
variable (i : Fin (n ^ (2 * g)))
variable (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (r + 1) (n ^ (2 * g)))
variable {f : Spec C ⟶ Spec (.of R)}
variable (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec C))
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C r P)
variable (e : A.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
variable (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback e.hom.left).sheaf ≅
  (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)
variable (hg : 0 < g) (hδ : ∀ k, 0 < δ k) (hN : 3 ≤ N)
variable (hunit : IsUnit (N : Γ(Spec C, ⊤)))
variable (level : A.abelian.FullLevel n) (D : ℕ) (hD : 0 < D)
variable (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} r P ≤ D)
variable (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < n ^ 2)
variable (hpoints : ∀ c : ULift.{u} (Fin (n ^ (2 * g))),
  (A.abelian.fullLevelGlobalSection level (Local.TorsionStableRankLift.liftedFullLevelLabelEnumeration c) ≫ e.hom.left) ≫
    HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap C C (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x c)
        (j.coordinate c.down) (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i j C x c))

include A I e eL hg hδ hN hunit level hD hdegree hlarge hpoints

theorem noetherianAuxiliaryTorsionConfiguration_hilbertFamily_recovery
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (ha : a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P ≫
      Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (P.eval (D : ℚ)).num.toNat = x) :
    HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) r) a
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P) = I.nativeHilbertFamily f := by
  let y := a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P
  have hy : y ≫ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (P.eval (D : ℚ)).num.toNat = x := by
    simpa only [y, Category.assoc] using ha
  have hc := TorsionStableCoordinates.auxiliaryTorsionStableChart_classifier_eq R C i j x A I e eL
    hg hδ hN hunit level D hD hlarge hpoints hdegree y hy
  have hp : (a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertParameterMap R i j D P) ≫
      HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver r D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} r D P) =
        HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f (TorsionStableCoordinates.configurationHilbertCoordinatePoint I D hdegree) := by
    have h := congrArg (fun z => a ≫ z) (Stable.ConfigurationLocus.stableConfigurationHilbert_parameter_condition R i j D P)
    have he : (a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertParameterMap R i j D P) ≫
        HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver r D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} r D P) =
      y ≫ Matrix.RankKernelClassifier.stableConfigurationPolynomialKernelClassifier R i j D (P.eval (D : ℚ)).num.toNat := by
      simpa only [y, Category.assoc] using h.symm
    exact he.trans hc
  change HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) r) a
    (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) r)
      (Stable.ConfigurationLocus.stableConfigurationHilbertParameterMap R i j D P)
      (HilbertScheme.Presentations.BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily r D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} r D P))) = _
  rw [← HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily_comp]
  exact I.hilbert_coordinate_lift_family f D hdegree (a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertParameterMap R i j D P) hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionConfigurationFamilyRecovery
