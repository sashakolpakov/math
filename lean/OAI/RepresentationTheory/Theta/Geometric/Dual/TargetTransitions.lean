import OAI.RepresentationTheory.Theta.Geometric.DualTransitionComparison
import OAI.RepresentationTheory.Theta.Geometric.ConstantTransitionValues
import OAI.RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart

/-! # Target Transitions -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.TargetTransitions

noncomputable section

/-! The target transition of the actual infinitesimal comparison is
the constant dual-number inclusion of the original theta ratio. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem dualThetaTarget_transition_constant
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z : Φ.space)
    (hf : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk z)))
    (hg : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk z)))
    (i j : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (U : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (W : X.left.Opens)
    (hiU : U ≤ ProductFrames.thetaQuotientOpen (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
      (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left i.1 i.2)
    (hjU : U ≤ ProductFrames.thetaQuotientOpen (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
      (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left j.1 j.2)
    (hiW : W ≤ ProductFrames.thetaQuotientOpen f.left g.left i.1 i.2)
    (hjW : W ≤ ProductFrames.thetaQuotientOpen f.left g.left j.1 j.2)
    (hU : (⊤ : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ).left.Opens) ≤ (AffineBaseChangeChart.dualConstantPoint X p).left ⁻¹ᵁ U)
    (hW : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W) :
    OpenSectionValues.dualSectionValue (AffineBaseChangeChart.dualConstantPoint X p).left U hU
      (IntrinsicFrame.TransitionUnits.frameTransitionUnit (AlgebraicQuotient.algebraicThetaQuotient (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
        (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left).sheaf U
        (QuotientIndexedFrames.thetaQuotientIndexedFrame (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
          (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left i U hiU)
        (QuotientIndexedFrames.thetaQuotientIndexedFrame (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
          (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left j U hjU) :
            Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, U)) =
      TrivSqZeroExt.inl (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.1 j.2 z / ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 z) := by
  have ht : AffineBaseChangeChart.dualConstantPoint X p ≫ snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X =
      toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ p := by simp [AffineBaseChangeChart.dualConstantPoint]
  have htf := congrArg Over.Hom.left ((Category.assoc (AffineBaseChangeChart.dualConstantPoint X p) _ f).symm.trans
    (congrArg (fun q => q ≫ f) ht))
  have htg := congrArg Over.Hom.left ((Category.assoc (AffineBaseChangeChart.dualConstantPoint X p) _ g).symm.trans
    (congrArg (fun q => q ≫ g) ht))
  have hd : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ p.left) ⁻¹ᵁ W := by
    intro u _
    change p.left ((Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))) u) ∈ W
    rwa [Subsingleton.elim ((Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))) u)
      (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)]
  exact (DualTransitionComparison.thetaQuotientFrame_transition_dualValue_congr (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left f.left
    (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left g.left (AffineBaseChangeChart.dualConstantPoint X p).left
    (toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ p).left htf htg i j U W hiU hjU hiW hjW hU hd).trans
      (ConstantTransitionValues.thetaQuotientFrame_transition_constantDual F G f g p z hf hg i j W hiW hjW hW hd)

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.TargetTransitions
