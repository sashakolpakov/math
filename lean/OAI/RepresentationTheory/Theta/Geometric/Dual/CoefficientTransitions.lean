import OAI.RepresentationTheory.Theta.Geometric.Dual.CoefficientRestrictions
import OAI.RepresentationTheory.Theta.Geometric.IsoDualFrameValues

/-! # Coefficient Transitions -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.CoefficientTransitions

noncomputable section

/-! Actual infinitesimal theta-isomorphism coefficients obey the native
source and target frame-transition equation on every common open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false in
theorem dualThetaIsoCoefficient_transition {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {n m : ℕ}
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m))
    (t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X ⟶ X)
    (e : (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
        (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left).sheaf)
    (i j : QuotientIndexedFrames.ThetaFrameIndex n m) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (W : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (hi : W ≤ IsoCoefficients.dualThetaIsoFrameOpen f g t i) (hj : W ≤ IsoCoefficients.dualThetaIsoFrameOpen f g t j)
    (hp : (BaseChangeReduction.dualBaseChangeReduction X).left (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈ W) :
    IsoCoefficients.dualThetaIsoCoefficient f g t e i p *
      OpenSectionValues.dualSectionValue (AffineBaseChangeChart.dualConstantPoint X p).left W (OpenRegularValues.dualConstantPoint_open_range X p W hp)
        (IntrinsicFrame.TransitionUnits.frameTransitionUnit (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf W
          (QuotientIndexedFrames.thetaQuotientIndexedFrame (t ≫ f).left (t ≫ g).left i W (hi.trans inf_le_left))
          (QuotientIndexedFrames.thetaQuotientIndexedFrame (t ≫ f).left (t ≫ g).left j W (hj.trans inf_le_left)) :
            Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, W)) =
    OpenSectionValues.dualSectionValue (AffineBaseChangeChart.dualConstantPoint X p).left W (OpenRegularValues.dualConstantPoint_open_range X p W hp)
        (IntrinsicFrame.TransitionUnits.frameTransitionUnit
          (AlgebraicQuotient.algebraicThetaQuotient (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
            (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left).sheaf W
          (QuotientIndexedFrames.thetaQuotientIndexedFrame (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
            (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left i W (hi.trans inf_le_right))
          (QuotientIndexedFrames.thetaQuotientIndexedFrame (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
            (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left j W (hj.trans inf_le_right)) :
              Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, W)) * IsoCoefficients.dualThetaIsoCoefficient f g t e j p := by
  rw [CoefficientRestrictions.dualThetaIsoCoefficient_value_on f g t e i p W hi hp,
    CoefficientRestrictions.dualThetaIsoCoefficient_value_on f g t e j p W hj hp]
  exact IsoDualFrameValues.moduleIsoFrameUnit_dualValue_transition e W _ _ _ _ _ _

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.CoefficientTransitions
