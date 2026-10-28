import OAI.RepresentationTheory.Theta.Geometric.DualTransitionComparison
import OAI.RepresentationTheory.Theta.Geometric.FrameTransitionFirstJet
import OAI.RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart

/-! # Source Transitions -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.SourceTransitions

noncomputable section

/-! The source transition of an actual infinitesimal theta comparison
is the first jet of the original consecutive theta ratio. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold

theorem dualThetaSource_transition_firstJet
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X ⟶ X) (p : Φ.space → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : Φ.space)
    (ht : AffineBaseChangeChart.dualConstantPoint X (p z) ≫ t = Intrinsic.MapFirstJet.nativeMapFirstJet X p z a)
    (hf : ∀ w, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (p w) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk w)))
    (hg : ∀ w, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (p w) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk w)))
    (hp : MDifferentiableAt (𝓘(ℂ, Φ.space))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z)
    (i j : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (U : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (W : X.left.Opens)
    (hiU : U ≤ ProductFrames.thetaQuotientOpen (t ≫ f).left (t ≫ g).left i.1 i.2)
    (hjU : U ≤ ProductFrames.thetaQuotientOpen (t ≫ f).left (t ≫ g).left j.1 j.2)
    (hiW : W ≤ ProductFrames.thetaQuotientOpen f.left g.left i.1 i.2)
    (hjW : W ≤ ProductFrames.thetaQuotientOpen f.left g.left j.1 j.2)
    (hU : (⊤ : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ).left.Opens) ≤ (AffineBaseChangeChart.dualConstantPoint X (p z)).left ⁻¹ᵁ U)
    (hW : (p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W) :
    OpenSectionValues.dualSectionValue (AffineBaseChangeChart.dualConstantPoint X (p z)).left U hU
      (IntrinsicFrame.TransitionUnits.frameTransitionUnit (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf U
        (QuotientIndexedFrames.thetaQuotientIndexedFrame (t ≫ f).left (t ≫ g).left i U hiU)
        (QuotientIndexedFrames.thetaQuotientIndexedFrame (t ≫ f).left (t ≫ g).left j U hjU) :
          Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, U)) =
      ScalarFirstJet.scalarFirstJet (fun w => ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.1 j.2 w / ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 w) z a := by
  have htf := congrArg Over.Hom.left ((Category.assoc (AffineBaseChangeChart.dualConstantPoint X (p z)) t f).symm.trans
    (congrArg (fun q => q ≫ f) ht))
  have htg := congrArg Over.Hom.left ((Category.assoc (AffineBaseChangeChart.dualConstantPoint X (p z)) t g).symm.trans
    (congrArg (fun q => q ≫ g) ht))
  exact (DualTransitionComparison.thetaQuotientFrame_transition_dualValue_congr (t ≫ f).left f.left (t ≫ g).left g.left
    (AffineBaseChangeChart.dualConstantPoint X (p z)).left (Intrinsic.MapFirstJet.nativeMapFirstJet X p z a).left htf htg i j U W
    hiU hjU hiW hjW hU (Intrinsic.MapFirstJet.nativeMapFirstJet_open_range X p z a W hW)).trans
      (FrameTransitionFirstJet.thetaQuotientFrame_transition_firstJet F G f g p hf hg i j W hiW hjW z a hp hW)

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.SourceTransitions
