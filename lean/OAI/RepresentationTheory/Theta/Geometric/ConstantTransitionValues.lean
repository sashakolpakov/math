import OAI.RepresentationTheory.Theta.Geometric.ConstantDualSectionValues
import OAI.RepresentationTheory.Theta.Geometric.QuotientIndexedFrames

/-! # Constant Transition Values -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConstantTransitionValues

noncomputable section

/-! Native theta-frame transitions at constant dual-number points have
the original complex ratio as their constant coefficient and zero
infinitesimal coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem thetaQuotientFrame_transition_constantDual
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z : Φ.space)
    (hf : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk z)))
    (hg : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk z)))
    (i j : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension) (W : X.left.Opens)
    (hi : W ≤ ProductFrames.thetaQuotientOpen f.left g.left i.1 i.2)
    (hj : W ≤ ProductFrames.thetaQuotientOpen f.left g.left j.1 j.2)
    (hp : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W)
    (hd : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ p.left) ⁻¹ᵁ W) :
    Dual.OpenSectionValues.dualSectionValue (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ p.left) W hd
      (IntrinsicFrame.TransitionUnits.frameTransitionUnit (AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf W
        (QuotientIndexedFrames.thetaQuotientIndexedFrame f.left g.left i W hi)
        (QuotientIndexedFrames.thetaQuotientIndexedFrame f.left g.left j W hj) : Γ(X.left, W)) =
      TrivSqZeroExt.inl (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.1 j.2 z / ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 z) :=
  (ConstantDualSectionValues.dualSectionValue_constant p.left W hp hd _).trans
    (congrArg TrivSqZeroExt.inl
      (QuotientIndexedFrames.thetaQuotientIndexedFrame_transition_value F G f g p z hf hg i j W hi hj hp))

end

end OAI.RepresentationTheory.Theta.Geometric.ConstantTransitionValues
