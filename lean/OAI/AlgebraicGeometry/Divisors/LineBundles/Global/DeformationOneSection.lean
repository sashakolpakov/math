import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.UnitParameter

/-! # Deformation One Section -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationOneSection.BundleCycles

noncomputable section

/-! The affine evaluations at one glue to an actual global section of
the deformation projection, with the original affine evaluation formula. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def deformationOneCocone : Cocone (directedCover X).functorOfLocallyDirected where
  pt := Deformation.BundleCycles.globalDeformation I
  ι := (restrictIsoSpec X).hom ≫
    Functor.whiskerRight (Deformation.UnitParameter.BundleCycles.deformationOneDiagram I).rightOp Scheme.Spec ≫
      (colimit.cocone (Deformation.BundleCycles.deformationGlueData I).functor).ι

def globalDeformationOneSection : X ⟶ Deformation.BundleCycles.globalDeformation I :=
  (directedCover X).isColimitCoconeOfLocallyDirected.desc (deformationOneCocone I)

theorem globalDeformationOneSection_on_chart (U : X.AffineZariskiSite) :
    U.1.ι ≫ globalDeformationOneSection I =
      DeformationProperties.BundleCycles.deformationChartSection I U ≫ (Deformation.BundleCycles.globalDeformationCover I).f U :=
  (directedCover X).isColimitCoconeOfLocallyDirected.fac (deformationOneCocone I) U

theorem globalDeformationOneSection_projection :
    globalDeformationOneSection I ≫ Deformation.BundleCycles.globalDeformationProjection I = 𝟙 X := by
  apply (directedCover X).hom_ext
  intro U
  rw [← Category.assoc, globalDeformationOneSection_on_chart, Category.assoc]
  change DeformationProperties.BundleCycles.deformationChartSection I U ≫
    ((Deformation.BundleCycles.deformationGlueData I).cover.f U ≫ (Deformation.BundleCycles.deformationGlueData I).toBase) = U.1.ι ≫ 𝟙 X
  have hc : (Deformation.BundleCycles.globalDeformationCover I).f U ≫ Deformation.BundleCycles.globalDeformationProjection I =
      (Deformation.BundleCycles.deformationGlueData I).natTrans.app U ≫ U.1.ι := (Deformation.BundleCycles.deformationGlueData I).ι_toBase U
  exact (congrArg (fun k => DeformationProperties.BundleCycles.deformationChartSection I U ≫ k) hc).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ U.1.ι) (DeformationProperties.BundleCycles.deformationChartSection_toBase I U)).trans
        ((Category.id_comp _).trans (Category.comp_id _).symm)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationOneSection.BundleCycles
