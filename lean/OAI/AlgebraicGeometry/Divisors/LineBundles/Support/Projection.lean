import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SupportDeformation

/-! # Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Projection.BundleCycles

noncomputable section

/-!
# LineBundleCycles: projection of the support deformation to the actual closed scheme

The quotient coefficient spectra are the standard affine charts of the
closed subscheme. Their constant maps glue to a projection from its
deformation, and evaluation at one proves this projection surjective.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I P : X.IdealSheafData)

/-- The standard affine coefficient chart in the actual closed support scheme. -/
def supportCoefficientChart (U : X.AffineZariskiSite) :
    Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) ⟶ P.subscheme := P.subschemeCover.f U

instance supportCoefficientChart_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion (supportCoefficientChart P U) := P.subschemeCover.openCover.map_prop U

theorem supportCoefficientChart_range (U : X.AffineZariskiSite) :
    (supportCoefficientChart P U).opensRange = P.subschemeι ⁻¹ᵁ U.1 :=
  P.opensRange_subschemeCover_map U

/-- The constants map from a support deformation chart to its coefficient spectrum. -/
def supportDeformationChartProjection (U : X.AffineZariskiSite) :
    (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U ⟶ Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) :=
  Spec.map (CommRingCat.ofHom (algebraMap ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))
    (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))))

/-- The chart projection regarded as a map to the whole closed support. -/
def supportDeformationChartToSupport (U : X.AffineZariskiSite) :
    (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U ⟶ P.subscheme :=
  supportDeformationChartProjection I P U ≫ supportCoefficientChart P U

theorem supportDeformationChartToSupport_toBase (U : X.AffineZariskiSite) :
    supportDeformationChartToSupport I P U ≫ P.subschemeι =
      (Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).natTrans.app U ≫ U.1.ι := by
  let a : Γ(X, U.1) ⟶ (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (P.ideal U))
  let b : (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U) ⟶
      (DeformationDiagram.BundleCycles.supportDeformationDiagram I P).obj (.op U) :=
    CommRingCat.ofHom (algebraMap ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))
      (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)))
  have hab : a ≫ b = (DeformationDiagram.BundleCycles.supportDeformationDiagramMap I P).app (.op U) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (DeformationDiagram.BundleCycles.supportDeformationDiagramMap_apply I P U r).symm
  have hP : supportCoefficientChart P U ≫ P.subschemeι =
      (Spec.map a ≫ U.2.isoSpec.inv) ≫ U.1.ι := P.subschemeCover_map_subschemeι U
  have hspec : Spec.map b ≫ Spec.map a =
      Spec.map ((DeformationDiagram.BundleCycles.supportDeformationDiagramMap I P).app (.op U)) :=
    (Spec.map_comp a b).symm.trans (congrArg Spec.map hab)
  change (Spec.map b ≫ supportCoefficientChart P U) ≫ P.subschemeι =
    (Spec.map ((DeformationDiagram.BundleCycles.supportDeformationDiagramMap I P).app (.op U)) ≫ U.2.isoSpec.inv) ≫ U.1.ι
  rw [Category.assoc, hP, ← Category.assoc, ← Category.assoc, hspec]
  rfl

/-- The chart maps to the support agree on every affine transition. -/
def supportProjectionCocone : Cocone (Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).functor where
  pt := P.subscheme
  ι.app U := supportDeformationChartToSupport I P U
  ι.naturality {U V} f := by
    apply (cancel_mono P.subschemeι).mp
    have h : (Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).functor.map f ≫
        ((Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).natTrans.app V ≫ V.1.ι) =
      (Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).natTrans.app U ≫ U.1.ι :=
      (((Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).natTrans ≫
        (directedCover X).functorOfLocallyDirectedHomBase).naturality f).trans (Category.comp_id _)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).functor.map f ≫ k)
        (supportDeformationChartToSupport_toBase I P V)).trans
      (h.trans ((supportDeformationChartToSupport_toBase I P U).symm.trans
        (congrArg (fun k => k ≫ P.subschemeι)
          (Category.comp_id (supportDeformationChartToSupport I P U)).symm))))

/-- The actual structural projection to the closed support scheme. -/
def globalSupportDeformationToSupport : Global.SupportDeformation.BundleCycles.globalSupportDeformation I P ⟶ P.subscheme :=
  colimit.desc _ (supportProjectionCocone I P)

theorem globalSupportDeformationToSupport_on_chart (U : X.AffineZariskiSite) :
    (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U ≫ globalSupportDeformationToSupport I P =
      supportDeformationChartToSupport I P U :=
  colimit.ι_desc (supportProjectionCocone I P) U

theorem globalSupportDeformationToSupport_toBase :
    globalSupportDeformationToSupport I P ≫ P.subschemeι = Global.SupportDeformation.BundleCycles.globalSupportDeformationProjection I P := by
  apply (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).hom_ext
  intro U
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ P.subschemeι) (globalSupportDeformationToSupport_on_chart I P U)).trans
    ((supportDeformationChartToSupport_toBase I P U).trans
      ((Global.SupportDeformation.BundleCycles.supportDeformationGlueData I P).ι_toBase U).symm))

/-- Evaluation at t = 1 on a support chart. -/
def supportDeformationChartSection (U : X.AffineZariskiSite) :
    Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) ⟶ (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U :=
  Spec.map (CommRingCat.ofHom (Global.DeformationProperties.BundleCycles.deformationAtOne (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)))

theorem supportDeformationChartSection_projection (U : X.AffineZariskiSite) :
    supportDeformationChartSection I P U ≫ supportDeformationChartProjection I P U = 𝟙 _ := by
  let a : (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U) ⟶
      (DeformationDiagram.BundleCycles.supportDeformationDiagram I P).obj (.op U) :=
    CommRingCat.ofHom (algebraMap ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))
      (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)))
  let b : (DeformationDiagram.BundleCycles.supportDeformationDiagram I P).obj (.op U) ⟶
      (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U) :=
    CommRingCat.ofHom (Global.DeformationProperties.BundleCycles.deformationAtOne (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
  have hab : a ≫ b = 𝟙 _ := CommRingCat.hom_ext (Global.DeformationProperties.BundleCycles.deformationAtOne_algebraMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
  exact (Spec.map_comp a b).symm.trans ((congrArg Spec.map hab).trans (Spec.map_id _))

/-- Every point of the actual support has a point above it at t = 1. -/
theorem globalSupportDeformationToSupport_surjective :
    Function.Surjective (globalSupportDeformationToSupport I P) := by
  intro x
  obtain ⟨U, y, hy⟩ := P.subschemeCover.openCover.exists_eq x
  let z := supportDeformationChartSection I P U y
  refine ⟨(Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U z, ?_⟩
  have h := congrArg (fun k => k z) (globalSupportDeformationToSupport_on_chart I P U)
  have hs := congrArg (fun k => k y) (supportDeformationChartSection_projection I P U)
  change supportDeformationChartProjection I P U z = y at hs
  change globalSupportDeformationToSupport I P ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U z) =
    supportCoefficientChart P U (supportDeformationChartProjection I P U z) at h
  exact h.trans ((congrArg (supportCoefficientChart P U) hs).trans hy)

/-- The support's standard affine opens pull back to the expected deformation charts. -/
theorem globalSupportDeformationToSupport_preimage (U : X.AffineZariskiSite) :
    globalSupportDeformationToSupport I P ⁻¹ᵁ (supportCoefficientChart P U).opensRange =
      ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U).opensRange := by
  rw [supportCoefficientChart_range, ← Scheme.Hom.comp_preimage,
    globalSupportDeformationToSupport_toBase, Global.SupportDeformation.BundleCycles.globalSupportDeformationProjection_preimage]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Projection.BundleCycles
