import OAI.RepresentationTheory.Theta.Geometric.Local.DualGauge
import OAI.RepresentationTheory.Theta.Geometric.Dual.GaugeCovariance

/-! # Dual Gauge Covariance -/

namespace OAI.RepresentationTheory.Theta.Geometric.Local.DualGaugeCovariance

noncomputable section

/-! The gauges extracted from the native isomorphism satisfy the exact
first-jet automorphy equation of the original theta factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem localDualThetaGauge_translates
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hdeg : G.degree = F.degree + 1)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X ⟶ X)
    (e : (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
        (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left).sheaf)
    (p : Φ.space → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : Φ.space) (l : Φ.periodIntegerLattice)
    (hperiod : p (z + l.val) = p z) (hJ : DifferentiableAt ℂ (J.value l) z)
    (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (hz : (Dual.BaseChangeReduction.dualBaseChangeReduction X).left ((p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈
      Dual.IsoCoefficients.dualThetaIsoFrameOpen f g t i)
    (hi : F.coordinate i.1 z ≠ 0) (hj : G.coordinate i.2 z ≠ 0) :
    DualGauge.localDualThetaGauge F G f g t e i (p (z + l.val)) (z + l.val) a * ScalarFirstJet.scalarFirstJet (J.value l) z a =
      TrivSqZeroExt.inl (J.value l z) * DualGauge.localDualThetaGauge F G f g t e i (p z) z a := by
  have hq := ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero F G i.1 i.2 z hi hj
  have hr := Dual.IsoCoefficients.dualThetaIsoCoefficient_isUnit f g t e i (p z) hz
  have hs := ScalarFirstJet.scalarFirstJet_isUnit (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2) z a hq
  have ht : IsUnit (TrivSqZeroExt.inl (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 z) : DualNumber ℂ) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hq)
  have hju : IsUnit (TrivSqZeroExt.inl (J.value l z) : DualNumber ℂ) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr (J.value_ne_zero l z))
  have hku := ScalarFirstJet.scalarFirstJet_isUnit (J.value l) z a (J.value_ne_zero l z)
  unfold DualGauge.localDualThetaGauge
  rw [hperiod, ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_translates F G hdeg i.1 i.2 l z,
    GaugeFirstJet.CM.Torus.AutomorphicTheta.consecutiveGauge_firstJet_translates F G hdeg i.1 i.2 l z a hi hJ, TrivSqZeroExt.inl_mul]
  exact Dual.GaugeCovariance.dualGauge_covariance _ _ _ _ _ hr hs ht hju hku

end

end OAI.RepresentationTheory.Theta.Geometric.Local.DualGaugeCovariance
