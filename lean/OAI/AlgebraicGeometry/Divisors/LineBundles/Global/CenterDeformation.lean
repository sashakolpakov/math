import OAI.AlgebraicGeometry.Divisors.LineBundles.SelfSupportDeformation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Projection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Specialization

/-! # Center Deformation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CenterDeformation.BundleCycles

noncomputable section

/-! The actual map from the center's self-deformation to its affine line,
and its agreement with the polynomial isomorphisms on all affine charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def globalCenterDeformationToLine : SupportDeformation.BundleCycles.globalSupportDeformation I I ⟶ AffineLine.Charts.BundleCycles.affineLine I.subscheme :=
  AffineSpace.homOfVector (Support.Projection.BundleCycles.globalSupportDeformationToSupport I I)
    (fun _ : PUnit => Support.Specialization.BundleCycles.globalSupportParameterSection I I)

theorem globalCenterDeformationToLine_over :
    globalCenterDeformationToLine I ≫ AffineLine.Charts.BundleCycles.affineLineProjection I.subscheme =
      Support.Projection.BundleCycles.globalSupportDeformationToSupport I I := AffineSpace.homOfVector_over _ _

theorem globalCenterDeformationToLine_coordinate :
    (globalCenterDeformationToLine I).appTop (AffineLine.Space.BundleCycles.affineLineCoordinate I.subscheme) =
      Support.Specialization.BundleCycles.globalSupportParameterSection I I := AffineSpace.homOfVector_appTop_coord _ _ _

def centerDeformationLineChart (U : X.AffineZariskiSite) :
    (SupportDeformation.BundleCycles.globalSupportDeformationCover I I).X U ⟶ AffineLine.Charts.BundleCycles.affineLine I.subscheme :=
  (SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso (I.ideal U)).hom ≫
    AffineSpace.map PUnit (Support.Projection.BundleCycles.supportCoefficientChart I U)

theorem centerDeformationLineChart_over (U : X.AffineZariskiSite) :
    centerDeformationLineChart I U ≫ AffineLine.Charts.BundleCycles.affineLineProjection I.subscheme =
      Support.Projection.BundleCycles.supportDeformationChartToSupport I I U := by
  change ((SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso (I.ideal U)).hom ≫
    AffineSpace.map PUnit (Support.Projection.BundleCycles.supportCoefficientChart I U)) ≫ _ = _
  have hm : AffineSpace.map PUnit (Support.Projection.BundleCycles.supportCoefficientChart I U) ≫ AffineLine.Charts.BundleCycles.affineLineProjection I.subscheme =
      AffineLine.Charts.BundleCycles.affineLineProjection (Spec ((Support.CoefficientDiagram.BundleCycles.supportCoefficientDiagram I).obj (.op U))) ≫ Support.Projection.BundleCycles.supportCoefficientChart I U :=
    AffineSpace.map_over (Support.Projection.BundleCycles.supportCoefficientChart I U)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso (I.ideal U)).hom ≫ k) hm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ Support.Projection.BundleCycles.supportCoefficientChart I U) (SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso_over (I.ideal U)))))

theorem centerDeformationLineChart_coordinate (U : X.AffineZariskiSite) :
    (centerDeformationLineChart I U).appTop (AffineLine.Space.BundleCycles.affineLineCoordinate I.subscheme) =
      Affine.Specialization.BundleCycles.affineDeformationParameterSection (Support.CoefficientDiagram.BundleCycles.supportCenterIdeal I I U) := by
  change ((SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso (I.ideal U)).hom ≫
    AffineSpace.map PUnit (Support.Projection.BundleCycles.supportCoefficientChart I U)).appTop
      (AffineSpace.coord I.subscheme PUnit.unit) = _
  change (SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso (I.ideal U)).hom.appTop
    ((AffineSpace.map PUnit (Support.Projection.BundleCycles.supportCoefficientChart I U)).appTop
      (AffineSpace.coord I.subscheme PUnit.unit)) = _
  exact (congrArg ((SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso (I.ideal U)).hom.appTop)
    (AffineSpace.map_appTop_coord (Support.Projection.BundleCycles.supportCoefficientChart I U) PUnit.unit)).trans
      (SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso_coordinate (I.ideal U))

theorem globalCenterDeformationToLine_on_chart (U : X.AffineZariskiSite) :
    (SupportDeformation.BundleCycles.globalSupportDeformationCover I I).f U ≫ globalCenterDeformationToLine I =
      centerDeformationLineChart I U := by
  apply AffineSpace.hom_ext
  · change ((SupportDeformation.BundleCycles.globalSupportDeformationCover I I).f U ≫ globalCenterDeformationToLine I) ≫
      AffineLine.Charts.BundleCycles.affineLineProjection I.subscheme = centerDeformationLineChart I U ≫ AffineLine.Charts.BundleCycles.affineLineProjection I.subscheme
    rw [Category.assoc, globalCenterDeformationToLine_over,
      Support.Projection.BundleCycles.globalSupportDeformationToSupport_on_chart, centerDeformationLineChart_over]
  · intro i
    cases i
    change ((SupportDeformation.BundleCycles.globalSupportDeformationCover I I).f U ≫ globalCenterDeformationToLine I).appTop
      (AffineLine.Space.BundleCycles.affineLineCoordinate I.subscheme) = (centerDeformationLineChart I U).appTop
        (AffineLine.Space.BundleCycles.affineLineCoordinate I.subscheme)
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, globalCenterDeformationToLine_coordinate,
      Support.Specialization.BundleCycles.globalSupportParameterSection_on_chart, centerDeformationLineChart_coordinate]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CenterDeformation.BundleCycles
