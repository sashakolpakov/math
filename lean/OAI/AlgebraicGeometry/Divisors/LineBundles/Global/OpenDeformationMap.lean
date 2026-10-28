import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationDiagram
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties

/-! # Open Deformation Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.OpenDeformationMap.BundleCycles

noncomputable section

/-! The actual affine chart maps of an open immersion glue to a morphism from the deformation of its pulled-back center to the original deformation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (I : Y.IdealSheafData)

def openDeformationMapCocone : Cocone (Deformation.BundleCycles.deformationGlueData (I.comap i)).functor where
  pt := Deformation.BundleCycles.globalDeformation I
  ι := Functor.whiskerRight (Open.DeformationDiagram.BundleCycles.openDeformationDiagramMap i I).rightOp Scheme.Spec ≫
    Functor.whiskerLeft (Open.AffineChartBase.BundleCycles.openAffineSiteImageFunctor i) (colimit.cocone (Deformation.BundleCycles.deformationGlueData I).functor).ι

def globalOpenDeformationMap : Deformation.BundleCycles.globalDeformation (I.comap i) ⟶ Deformation.BundleCycles.globalDeformation I :=
  colimit.desc _ (openDeformationMapCocone i I)

theorem globalOpenDeformationMap_on_chart (U : X.AffineZariskiSite) :
    (Deformation.BundleCycles.globalDeformationCover (I.comap i)).f U ≫ globalOpenDeformationMap i I =
      Spec.map (CommRingCat.ofHom (Open.DeformationDiagram.BundleCycles.openDeformationRingMap i I U)) ≫
        (Deformation.BundleCycles.globalDeformationCover I).f (Open.AffineChartBase.BundleCycles.openAffineSiteImage i U) :=
  colimit.ι_desc (openDeformationMapCocone i I) U

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.OpenDeformationMap.BundleCycles
