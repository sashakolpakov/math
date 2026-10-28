import OAI.RepresentationTheory.Theta.Geometric.Dual.CoefficientTransitions
import OAI.RepresentationTheory.Theta.Geometric.Dual.SourceTransitions
import OAI.RepresentationTheory.Theta.Geometric.Dual.TargetTransitions
import OAI.RepresentationTheory.Theta.Geometric.Dual.IsoCoordinates

/-! # Analytic Transitions -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.AnalyticTransitions

noncomputable section

/-! The coefficients read from the actual infinitesimal isomorphism
satisfy the original theta-ratio transition law, including its first jet. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false in
theorem dualThetaIsoCoefficient_theta_transition
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
    (ht : AffineBaseChangeChart.dualConstantPoint X (p z) ≫ t = Intrinsic.MapFirstJet.nativeMapFirstJet X p z a)
    (hf : ∀ w, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (p w) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk w)))
    (hg : ∀ w, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (p w) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk w)))
    (hp : MDifferentiableAt (𝓘(ℂ, Φ.space))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z)
    (i j : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (hi : F.coordinate i.1 z ≠ 0 ∧ G.coordinate i.2 z ≠ 0)
    (hj : F.coordinate j.1 z ≠ 0 ∧ G.coordinate j.2 z ≠ 0) :
    IsoCoefficients.dualThetaIsoCoefficient f g t e i (p z) *
        ScalarFirstJet.scalarFirstJet (fun w => ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.1 j.2 w / ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 w) z a =
      TrivSqZeroExt.inl (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.1 j.2 z / ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 z) *
        IsoCoefficients.dualThetaIsoCoefficient f g t e j (p z) := by
  let U := IsoCoefficients.dualThetaIsoFrameOpen f g t i ⊓ IsoCoefficients.dualThetaIsoFrameOpen f g t j
  let W := ProductFrames.thetaQuotientOpen f.left g.left i.1 i.2 ⊓ ProductFrames.thetaQuotientOpen f.left g.left j.1 j.2
  have hred := SourceReduction.dualSource_reduction_eq X p z a t ht
  have hU : (BaseChangeReduction.dualBaseChangeReduction X).left ((p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈ U :=
    ⟨(IsoCoordinates.dualThetaIsoFrameOpen_mem F G f g t (p z) z hred (hf z) (hg z) i).mpr hi,
      (IsoCoordinates.dualThetaIsoFrameOpen_mem F G f g t (p z) z hred (hf z) (hg z) j).mpr hj⟩
  have hW : (p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W :=
    ⟨⟨(ProductValues.thetaCoordinateOpen_mem_of_point F f (p z) z (hf z) i.1).mpr hi.1,
      (ProductValues.thetaCoordinateOpen_mem_of_point G g (p z) z (hg z) i.2).mpr hi.2⟩,
      ⟨(ProductValues.thetaCoordinateOpen_mem_of_point F f (p z) z (hf z) j.1).mpr hj.1,
        (ProductValues.thetaCoordinateOpen_mem_of_point G g (p z) z (hg z) j.2).mpr hj.2⟩⟩
  have hS := SourceTransitions.dualThetaSource_transition_firstJet F G f g t p z a ht hf hg hp i j U W
    (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) inf_le_left inf_le_right
    (OpenRegularValues.dualConstantPoint_open_range X (p z) U hU) hW
  have hT := TargetTransitions.dualThetaTarget_transition_constant F G f g (p z) z (hf z) (hg z) i j U W
    (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) inf_le_left inf_le_right
    (OpenRegularValues.dualConstantPoint_open_range X (p z) U hU) hW
  have H := CoefficientTransitions.dualThetaIsoCoefficient_transition f g t e i j (p z) U inf_le_left inf_le_right hU
  rw [hS, hT] at H
  exact H

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.AnalyticTransitions
