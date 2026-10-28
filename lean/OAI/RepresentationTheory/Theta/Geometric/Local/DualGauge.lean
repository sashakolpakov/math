import OAI.RepresentationTheory.Theta.Geometric.Dual.IsoCoefficients
import OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet

/-! # Dual Gauge -/

namespace OAI.RepresentationTheory.Theta.Geometric.Local.DualGauge

noncomputable section

/-! The local infinitesimal comparison gauge is formed directly from
the native isomorphism coefficient, the original theta ratio, and its
actual first jet. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet.CM.Torus.AutomorphicTheta
open scoped _root_.Manifold

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X ⟶ X)
    (e : (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
        (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left).sheaf)

def localDualThetaGauge (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : Φ.space) : DualNumber ℂ :=
  Dual.IsoCoefficients.dualThetaIsoCoefficient f g t e i p * TrivSqZeroExt.inl (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 z) *
    (ScalarFirstJet.scalarFirstJet (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2) z a)⁻¹

theorem localDualThetaGauge_isUnit (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : Φ.space)
    (hp : (Dual.BaseChangeReduction.dualBaseChangeReduction X).left (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈
      Dual.IsoCoefficients.dualThetaIsoFrameOpen f g t i)
    (hi : F.coordinate i.1 z ≠ 0) (hj : G.coordinate i.2 z ≠ 0) :
    IsUnit (localDualThetaGauge F G f g t e i p z a) := by
  have hq := ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero F G i.1 i.2 z hi hj
  have ht : IsUnit (TrivSqZeroExt.inl (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 z) : DualNumber ℂ) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hq)
  exact ((Dual.IsoCoefficients.dualThetaIsoCoefficient_isUnit f g t e i p hp).mul ht).mul
    (TrivSqZeroExt.isUnit_inv_iff.mpr (ScalarFirstJet.scalarFirstJet_isUnit _ z a hq))

theorem localDualThetaGauge_differentiableAt [IsIntegral X.left] [Smooth X.hom]
    (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (p : Φ.space → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : Φ.space)
    (hp : MDifferentiableAt (𝓘(ℂ, Φ.space))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z)
    (hz : (Dual.BaseChangeReduction.dualBaseChangeReduction X).left ((p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈
      Dual.IsoCoefficients.dualThetaIsoFrameOpen f g t i)
    (hi : F.coordinate i.1 z ≠ 0) (hj : G.coordinate i.2 z ≠ 0) :
    Dual.CoefficientHolomorphic.DualCoefficientDifferentiableAt (fun w => localDualThetaGauge F G f g t e i (p w) w a) z := by
  have hr := Dual.IsoCoefficients.dualThetaIsoCoefficient_differentiableAt f g t e i p z hp hz
  have ht : Dual.CoefficientHolomorphic.DualCoefficientDifferentiableAt
      (fun w => (TrivSqZeroExt.inl (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 w) : DualNumber ℂ)) z :=
    ⟨ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_differentiableAt F G i.1 i.2 z hi, differentiableAt_const _⟩
  have hs : Dual.CoefficientHolomorphic.DualCoefficientDifferentiableAt
      (fun w => ScalarFirstJet.scalarFirstJet (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2) w a) z :=
    ⟨ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_differentiableAt F G i.1 i.2 z hi,
      GaugeDerivativeHolomorphic.CM.Torus.AutomorphicTheta.consecutiveGauge_directionalDerivative_differentiableAt F G i.1 i.2 z a hi⟩
  exact Dual.CoefficientHolomorphic.dualCoefficientDifferentiableAt_mul _ _ z
    (Dual.CoefficientHolomorphic.dualCoefficientDifferentiableAt_mul _ _ z hr ht)
    (Dual.CoefficientHolomorphic.dualCoefficientDifferentiableAt_inv _ z hs (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero F G i.1 i.2 z hi hj))

end

end OAI.RepresentationTheory.Theta.Geometric.Local.DualGauge
