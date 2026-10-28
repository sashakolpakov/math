import OAI.RepresentationTheory.Theta.Geometric.Dual.IsoCoefficients

/-! # Iso Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.IsoCoordinates

noncomputable section

/-! The common infinitesimal theta-frame domains are exactly the
original nonzero theta-coordinate domains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem dualThetaIsoFrameOpen_mem
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X ⟶ X) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z : Φ.space)
    (ht : p ≫ BaseChangeReduction.dualBaseChangeReduction X ≫ t = p)
    (hf : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk z)))
    (hg : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk z)))
    (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension) :
    (BaseChangeReduction.dualBaseChangeReduction X).left (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈ IsoCoefficients.dualThetaIsoFrameOpen f g t i ↔
      F.coordinate i.1 z ≠ 0 ∧ G.coordinate i.2 z ≠ 0 := by
  have hS : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map t (p ≫ BaseChangeReduction.dualBaseChangeReduction X) = p :=
    (Category.assoc _ _ _).trans ht
  have hT : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X)
      (p ≫ BaseChangeReduction.dualBaseChangeReduction X) = p :=
    (Category.assoc _ _ _).trans (SourceReduction.dualTarget_reduction_eq X p)
  have H := IsoGaugeCompatibility.thetaIsoFrameOpen_mem F G (t ≫ f) (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f)
    (t ≫ g) (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g) (p ≫ BaseChangeReduction.dualBaseChangeReduction X) z z
    ((congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) hS).trans hf)
    ((congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g) hS).trans hg)
    ((congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) hT).trans hf)
    ((congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g) hT).trans hg) (i, i)
  change ((BaseChangeReduction.dualBaseChangeReduction X).left (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈
    IsoCoefficients.dualThetaIsoFrameOpen f g t i ↔
      (F.coordinate i.1 z ≠ 0 ∧ G.coordinate i.2 z ≠ 0) ∧
        (F.coordinate i.1 z ≠ 0 ∧ G.coordinate i.2 z ≠ 0)) at H
  exact H.trans ⟨And.left, fun h => ⟨h, h⟩⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.IsoCoordinates
