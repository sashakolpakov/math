import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.OpenSectionFirstJet
import OAI.RepresentationTheory.Theta.Geometric.QuotientIndexedFrames

/-! # Frame Transition First Jet -/

namespace OAI.RepresentationTheory.Theta.Geometric.FrameTransitionFirstJet

noncomputable section

/-! The actual native theta-frame transition, evaluated at the original
period jet, is exactly the first jet of its original analytic ratio. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold _root_.Topology

theorem thetaQuotientFrame_transition_firstJet
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (p : Φ.space → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hf : ∀ w, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (p w) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk w)))
    (hg : ∀ w, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (p w) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk w)))
    (i j : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension) (W : X.left.Opens)
    (hi : W ≤ ProductFrames.thetaQuotientOpen f.left g.left i.1 i.2)
    (hj : W ≤ ProductFrames.thetaQuotientOpen f.left g.left j.1 j.2) (z a : Φ.space)
    (hp : MDifferentiableAt (𝓘(ℂ, Φ.space))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z)
    (hz : (p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W) :
    Dual.OpenSectionValues.dualSectionValue (Intrinsic.MapFirstJet.nativeMapFirstJet X p z a).left W
      (Intrinsic.MapFirstJet.nativeMapFirstJet_open_range X p z a W hz)
      (IntrinsicFrame.TransitionUnits.frameTransitionUnit (AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf W
        (QuotientIndexedFrames.thetaQuotientIndexedFrame f.left g.left i W hi)
        (QuotientIndexedFrames.thetaQuotientIndexedFrame f.left g.left j W hj) : Γ(X.left, W)) =
      ScalarFirstJet.scalarFirstJet (fun w => ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.1 j.2 w /
        ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 w) z a := by
  let s : Γ(X.left, W) :=
    (IntrinsicFrame.TransitionUnits.frameTransitionUnit (AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf W
      (QuotientIndexedFrames.thetaQuotientIndexedFrame f.left g.left i W hi)
      (QuotientIndexedFrames.thetaQuotientIndexedFrame f.left g.left j W hj) : Γ(X.left, W))
  have hmem : ∀ᶠ w in 𝓝 z, (p w).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W :=
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying.continuousAt.comp hp.continuousAt)
      (W.isOpen.mem_nhds hz)
  have heq : OpenRegularFunctionValues.openRegularFunctionValue X W s ∘ p =ᶠ[𝓝 z]
      fun w => ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.1 j.2 w / ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 w := by
    filter_upwards [hmem] with w hw
    exact (OpenRegularFunctionValues.openRegularFunctionValue_of_mem X W s (p w) hw).trans
      (QuotientIndexedFrames.thetaQuotientIndexedFrame_transition_value F G f g (p w) w (hf w) (hg w) i j W hi hj hw)
  exact (Intrinsic.OpenSectionFirstJet.nativeOpenSectionValue_firstJet X W s p z a hp hz).trans
    (ScalarFirstJetLocality.scalarFirstJet_congr _ _ z a heq)

end

end OAI.RepresentationTheory.Theta.Geometric.FrameTransitionFirstJet
