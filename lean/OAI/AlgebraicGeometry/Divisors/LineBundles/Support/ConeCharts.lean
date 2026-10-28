import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Specialization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeNaturality

/-! # Cone Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.ConeCharts.BundleCycles

noncomputable section

/-!
# LineBundleCycles: affine normal-cone charts of the global support fiber

The actual local normal cones map into the pulled-back global fiber.
Pullback cancellation proves these are open immersion charts and that
they cover the fiber, including for singular and nonreduced centers.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I P : X.IdealSheafData)

instance globalNormalConeChartMap_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion (Global.Specialization.BundleCycles.globalNormalConeChartMap I U) := by
  have hs : IsOpenImmersion ((Global.SpecialFiber.BundleCycles.globalSpecialFiberCover I).f U) := (Global.SpecialFiber.BundleCycles.globalSpecialFiberCover I).map_prop U
  exact @IsOpenImmersion.comp _ _ _ (Global.SpecialFiber.BundleCycles.globalSpecialFiberNormalConeChart I U).hom
    ((Global.SpecialFiber.BundleCycles.globalSpecialFiberCover I).f U) inferInstance hs

/-- The affine normal-cone chart is cartesian over its ambient deformation chart. -/
theorem globalNormalConeChart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (Affine.Specialization.BundleCycles.normalConeFiberInclusion (I.ideal U)) (Global.Specialization.BundleCycles.globalNormalConeChartMap I U)
      ((Global.Deformation.BundleCycles.globalDeformationCover I).f U) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I) := by
  let a : CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) ⟶
      CommRingCat.of (SpecialFiber.BundleCycles.DeformationSpecialRing (I.ideal U)) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))
  let b : CommRingCat.of (SpecialFiber.BundleCycles.DeformationSpecialRing (I.ideal U)) ⟶
      CommRingCat.of (Normal.Cone.BundleCycles.NormalConeRing (I.ideal U)) :=
    CommRingCat.ofHom (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv (I.ideal U)).symm.toRingHom
  have hq : (Global.SpecialFiber.BundleCycles.globalSpecialFiberNormalConeChart I U).hom ≫ Spec.map a =
      Affine.Specialization.BundleCycles.normalConeFiberInclusion (I.ideal U) := (Spec.map_comp a b).symm
  apply (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_chart_isPullback I U).of_iso'
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberNormalConeChart I U) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · exact hq.trans (Category.comp_id _).symm
  · exact (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The local support cone is the fiber over the support deformation chart. -/
theorem supportNormalConeChart_outer_isPullback (U : X.AffineZariskiSite) :
    IsPullback (Affine.Specialization.BundleCycles.normalConeFiberInclusion (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
      (CycleSpecialization.BundleCycles.closedSupportNormalConeInclusion (I.ideal U) (P.ideal U) ≫ Global.Specialization.BundleCycles.globalNormalConeChartMap I U)
      ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U ≫ Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P)
      (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I) := by
  have h := (Normal.ConeNaturality.BundleCycles.closedSupportNormalCone_isPullback (I.ideal U) (P.ideal U)).paste_vert
    (globalNormalConeChart_isPullback I U)
  exact (congrArg (fun k => IsPullback (Affine.Specialization.BundleCycles.normalConeFiberInclusion (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
    (CycleSpecialization.BundleCycles.closedSupportNormalConeInclusion (I.ideal U) (P.ideal U) ≫ Global.Specialization.BundleCycles.globalNormalConeChartMap I U)
    k (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)) (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap_on_chart I P U)).mpr h

/-- The canonical local normal cone as a chart of the actual global support fiber. -/
def globalSupportNormalConeChartMap (U : X.AffineZariskiSite) :
    Normal.Cone.BundleCycles.affineNormalCone (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) ⟶ Specialization.BundleCycles.globalSupportSpecialFiber I P :=
  pullback.lift
    (Affine.Specialization.BundleCycles.normalConeFiberInclusion (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) ≫ (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U)
    (CycleSpecialization.BundleCycles.closedSupportNormalConeInclusion (I.ideal U) (P.ideal U) ≫ Global.Specialization.BundleCycles.globalNormalConeChartMap I U)
    ((Category.assoc _ _ _).trans (supportNormalConeChart_outer_isPullback I P U).w)

theorem globalSupportNormalConeChartMap_fst (U : X.AffineZariskiSite) :
    globalSupportNormalConeChartMap I P U ≫ Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P =
      Affine.Specialization.BundleCycles.normalConeFiberInclusion (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) ≫ (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U :=
  pullback.lift_fst _ _ _

theorem globalSupportNormalConeChartMap_snd (U : X.AffineZariskiSite) :
    globalSupportNormalConeChartMap I P U ≫ Specialization.BundleCycles.globalSupportSpecialFiberMap I P =
      CycleSpecialization.BundleCycles.closedSupportNormalConeInclusion (I.ideal U) (P.ideal U) ≫ Global.Specialization.BundleCycles.globalNormalConeChartMap I U :=
  pullback.lift_snd _ _ _

/-- Each local support cone is the inverse image of the support deformation chart. -/
theorem globalSupportNormalConeChart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (Affine.Specialization.BundleCycles.normalConeFiberInclusion (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
      (globalSupportNormalConeChartMap I P U) ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U)
      (Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P) := by
  have h := (supportNormalConeChart_outer_isPullback I P U).flip
  have h' : IsPullback (globalSupportNormalConeChartMap I P U ≫ Specialization.BundleCycles.globalSupportSpecialFiberMap I P)
      (Affine.Specialization.BundleCycles.normalConeFiberInclusion (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)
      ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U ≫ Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) :=
    (congrArg (fun k => IsPullback k (Affine.Specialization.BundleCycles.normalConeFiberInclusion (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
      (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I) ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U ≫ Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P))
      (globalSupportNormalConeChartMap_snd I P U)).mpr h
  exact (h'.of_right (globalSupportNormalConeChartMap_fst I P U)
    (IsPullback.of_hasPullback (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)).flip).flip

/-- The same support cone is the inverse image in the ambient normal-cone chart. -/
theorem globalSupportNormalConeChart_ambient_isPullback (U : X.AffineZariskiSite) :
    IsPullback (CycleSpecialization.BundleCycles.closedSupportNormalConeInclusion (I.ideal U) (P.ideal U))
      (globalSupportNormalConeChartMap I P U) (Global.Specialization.BundleCycles.globalNormalConeChartMap I U)
      (Specialization.BundleCycles.globalSupportSpecialFiberMap I P) := by
  have h := (globalSupportNormalConeChart_isPullback I P U).paste_horiz
    (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap_chart_isPullback I P U)
  have ha := (congrArg (fun k => IsPullback k (globalSupportNormalConeChartMap I P U)
      ((Global.Deformation.BundleCycles.globalDeformationCover I).f U)
      (Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P ≫ Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P))
    (Normal.ConeNaturality.BundleCycles.closedSupportNormalCone_isPullback (I.ideal U) (P.ideal U)).w).mp h
  have hb := (congrArg (fun k => IsPullback
      (CycleSpecialization.BundleCycles.closedSupportNormalConeInclusion (I.ideal U) (P.ideal U) ≫ Affine.Specialization.BundleCycles.normalConeFiberInclusion (I.ideal U))
      (globalSupportNormalConeChartMap I P U) ((Global.Deformation.BundleCycles.globalDeformationCover I).f U) k)
    (pullback.condition (f := Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (g := Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I))).mp ha
  exact hb.of_right (globalSupportNormalConeChartMap_snd I P U).symm
    (globalNormalConeChart_isPullback I U)

instance globalSupportNormalConeChartMap_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion (globalSupportNormalConeChartMap I P U) := by
  let h := globalSupportNormalConeChart_isPullback I P U
  have hs : IsOpenImmersion (pullback.snd ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U)
      (Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P)) := inferInstance
  have hc : IsOpenImmersion
      (h.isoPullback.hom ≫ pullback.snd ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U)
        (Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P)) :=
    @IsOpenImmersion.comp _ _ _ h.isoPullback.hom
      (pullback.snd ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U) (Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P))
      inferInstance hs
  exact (congrArg (fun k => IsOpenImmersion k) h.isoPullback_hom_snd).mp hc

/-- The actual affine normal cones cover the entire global support fiber. -/
def globalSupportNormalConeCover : (Specialization.BundleCycles.globalSupportSpecialFiber I P).OpenCover :=
  Scheme.Cover.mkOfCovers X.AffineZariskiSite
    (fun U => Normal.Cone.BundleCycles.affineNormalCone (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
    (globalSupportNormalConeChartMap I P)
    (by
      intro x
      obtain ⟨U, y, hy⟩ := (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).exists_eq
        (Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P x)
      obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
        (globalSupportNormalConeChart_isPullback I P U) y x hy
      exact ⟨U, z, hz⟩)
    (globalSupportNormalConeChartMap_isOpenImmersion I P)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.ConeCharts.BundleCycles
