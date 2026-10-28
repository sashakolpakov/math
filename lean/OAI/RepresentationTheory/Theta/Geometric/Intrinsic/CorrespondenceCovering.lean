import OAI.RepresentationTheory.Theta.Geometric.Finite.EtaleAnalyticCover
import OAI.RepresentationTheory.Theta.Geometric.ComponentVarieties

/-! # Correspondence Covering -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! TateComparison's original complex correspondence source maps are covering maps.
The projective target comes from the original IntegralModel geometry. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.complexSpaceProjectivePresentation (hg : D.pel.HasIntegralModelGeometry) :
    AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexSpace.left D.pel.complexSpace.hom := by
  let P := ComponentVarieties.RelativeProjective.complexProjectivePresentation
    (Classical.choice hg.projective) D.pel.complexPoint
  let e := (Over.pullbackComp D.pel.complexGenericPoint D.pel.generic).app D.pel.model.space
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).map e.inv))
  exact
    { ambientDimension := P.ambientDimension
      embedding := e.inv.left ≫ P.embedding
      closedImmersion := inferInstanceAs (IsClosedImmersion (e.inv.left ≫ P.embedding))
      over_base := (Category.assoc _ _ _).trans
        ((congrArg (fun k => e.inv.left ≫ k) P.over_base).trans e.inv.w) }

theorem Data.ActiveHeckeThetaData.complexSpace_smooth (hg : D.pel.HasIntegralModelGeometry) : Smooth D.pel.complexSpace.hom := by
  have : Smooth D.pel.model.space.hom := hg.smooth
  have : Smooth D.pel.space.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd D.pel.model.space.hom D.pel.generic)
    infer_instance
  change Smooth (CategoryTheory.Limits.pullback.snd D.pel.space.hom D.pel.complexGenericPoint)
  infer_instance

theorem Data.ActiveHeckeThetaData.correspondenceSource_isCoveringMap (hg : D.pel.HasIntegralModelGeometry) (t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s) :
    IsCoveringMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (D.pel.complexCorrespondence t).source) := by
  have : Smooth D.pel.complexSpace.hom := D.complexSpace_smooth hg
  have : IsFinite (D.pel.complexCorrespondence t).source.left := (D.pel.complexCorrespondence t).finite
  have : Etale (D.pel.complexCorrespondence t).source.left := (D.pel.complexCorrespondence t).etale
  exact Geometric.Finite.EtaleAnalyticCover.finiteEtale_projectiveTarget_isCoveringMap
    (X := (D.pel.complexCorrespondence t).cover) (Y := D.pel.complexSpace)
    (D.complexSpaceProjectivePresentation hg) (D.pel.complexCorrespondence t).source

theorem Data.ActiveHeckeThetaData.correspondenceSource_finite_fiber (hg : D.pel.HasIntegralModelGeometry) (t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace) :
    ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (D.pel.complexCorrespondence t).source) ⁻¹' {x}).Finite := by
  have : Smooth D.pel.complexSpace.hom := D.complexSpace_smooth hg
  have : IsFinite (D.pel.complexCorrespondence t).source.left := (D.pel.complexCorrespondence t).finite
  have : Etale (D.pel.complexCorrespondence t).source.left := (D.pel.complexCorrespondence t).etale
  exact Geometric.Finite.EtaleAnalyticCover.finiteEtale_projectiveTarget_finite_fiber
    (X := (D.pel.complexCorrespondence t).cover) (Y := D.pel.complexSpace)
    (D.complexSpaceProjectivePresentation hg) (D.pel.complexCorrespondence t).source x

end

end OAI.RepresentationTheory.Theta.Geometric
