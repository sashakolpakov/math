import OAI.RepresentationTheory.Theta.Geometric.Dual.AnalyticTransitions
import OAI.RepresentationTheory.Theta.Geometric.Local.DualGauge
import OAI.RepresentationTheory.Theta.Geometric.Dual.GaugeCovariance

/-! # Dual Gauge Compatibility -/

namespace OAI.RepresentationTheory.Theta.Geometric.Local.DualGaugeCompatibility

noncomputable section

/-! The local gauges extracted from the actual infinitesimal theta
isomorphism agree on every overlap of the original theta-coordinate
domains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold

theorem localDualThetaGauge_compatible
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X ⟶ X)
    (e : (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
        (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left).sheaf)
    (p : Φ.space → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : Φ.space)
    (ht : Dual.AffineBaseChangeChart.dualConstantPoint X (p z) ≫ t = Intrinsic.MapFirstJet.nativeMapFirstJet X p z a)
    (hf : ∀ w, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (p w) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk w)))
    (hg : ∀ w, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (p w) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk w)))
    (hp : MDifferentiableAt (𝓘(ℂ, Φ.space))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z)
    (i j : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (hi : F.coordinate i.1 z ≠ 0 ∧ G.coordinate i.2 z ≠ 0)
    (hj : F.coordinate j.1 z ≠ 0 ∧ G.coordinate j.2 z ≠ 0) :
    DualGauge.localDualThetaGauge F G f g t e i (p z) z a = DualGauge.localDualThetaGauge F G f g t e j (p z) z a := by
  have hqi := ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero F G i.1 i.2 z hi.1 hi.2
  have hqj := ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero F G j.1 j.2 z hj.1 hj.2
  have hred := Dual.SourceReduction.dualSource_reduction_eq X p z a t ht
  have hRi := Dual.IsoCoefficients.dualThetaIsoCoefficient_isUnit f g t e i (p z)
    ((Dual.IsoCoordinates.dualThetaIsoFrameOpen_mem F G f g t (p z) z hred (hf z) (hg z) i).mpr hi)
  have hRj := Dual.IsoCoefficients.dualThetaIsoCoefficient_isUnit f g t e j (p z)
    ((Dual.IsoCoordinates.dualThetaIsoFrameOpen_mem F G f g t (p z) z hred (hf z) (hg z) j).mpr hj)
  have hTi : IsUnit (TrivSqZeroExt.inl (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 z) : DualNumber ℂ) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hqi)
  have hTj : IsUnit (TrivSqZeroExt.inl (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.1 j.2 z) : DualNumber ℂ) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hqj)
  have H := Dual.AnalyticTransitions.dualThetaIsoCoefficient_theta_transition F G f g t e p z a ht hf hg hp i j hi hj
  rw [ScalarFirstJet.scalarFirstJet_div _ _ z a (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_differentiableAt F G j.1 j.2 z hj.1)
    (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_differentiableAt F G i.1 i.2 z hi.1) hqi] at H
  have hratio : (TrivSqZeroExt.inl (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.1 j.2 z / ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 z) :
      DualNumber ℂ) = TrivSqZeroExt.inl (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.1 j.2 z) *
        (TrivSqZeroExt.inl (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 z) : DualNumber ℂ)⁻¹ := by
    simp only [div_eq_mul_inv, TrivSqZeroExt.inl_mul, TrivSqZeroExt.inv_inl]
  rw [hratio] at H
  exact Dual.GaugeCovariance.dualGauge_independent _ _ _ _ _ _ hRi hRj
    (ScalarFirstJet.scalarFirstJet_isUnit _ z a hqi) (ScalarFirstJet.scalarFirstJet_isUnit _ z a hqj) hTi hTj H

end

end OAI.RepresentationTheory.Theta.Geometric.Local.DualGaugeCompatibility
