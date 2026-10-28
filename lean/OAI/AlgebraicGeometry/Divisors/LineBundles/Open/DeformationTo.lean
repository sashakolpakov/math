import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.OpenDeformationMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.AffineChartBase
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.PuncturedLaurentChart
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization

/-! # Deformation To -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationTo.BundleCycles

noncomputable section

section

/-! The deformation charts of an actual open immersion have exactly the expected base map and open image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (I : Y.IdealSheafData)
    (U : X.AffineZariskiSite)

instance openDeformationChartMap_isIso :
    IsIso (Spec.map (CommRingCat.ofHom (DeformationDiagram.BundleCycles.openDeformationRingMap i I U))) :=
  isIso_SpecMap_iff.mpr (DeformationDiagram.BundleCycles.openDeformationRingMap_bijective i I U)

def openDeformationChart : Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra ((I.comap i).ideal U))) ⟶ Global.Deformation.BundleCycles.globalDeformation I :=
  Spec.map (CommRingCat.ofHom (DeformationDiagram.BundleCycles.openDeformationRingMap i I U)) ≫
    (Global.Deformation.BundleCycles.globalDeformationCover I).f (AffineChartBase.BundleCycles.openAffineSiteImage i U)

instance openDeformationChart_open : IsOpenImmersion (openDeformationChart i I U) := by
  exact @IsOpenImmersion.comp _ _ _
    (Spec.map (CommRingCat.ofHom (DeformationDiagram.BundleCycles.openDeformationRingMap i I U)))
    ((Global.Deformation.BundleCycles.globalDeformationCover I).f (AffineChartBase.BundleCycles.openAffineSiteImage i U))
    inferInstance ((Global.Deformation.BundleCycles.globalDeformationCover I).map_prop _)

theorem openDeformationChart_baseSquare :
    Spec.map (CommRingCat.ofHom (DeformationDiagram.BundleCycles.openDeformationRingMap i I U)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, (AffineChartBase.BundleCycles.openAffineSiteImage i U).1)
        (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal (AffineChartBase.BundleCycles.openAffineSiteImage i U))))) =
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (Deformation.Iff.BundleCycles.deformationAlgebra ((I.comap i).ideal U)))) ≫
      Spec.map (i.appIso U.1).hom := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact Deformation.Maps.BundleCycles.deformationMap_algebraMap _ _ _
    (Ideal.map_le_iff_le_comap.mp (AffineChartBase.BundleCycles.openAffineSiteImage_ideal i I U).symm.le) r

theorem openDeformationChart_toBase :
    openDeformationChart i I U ≫ Global.Deformation.BundleCycles.globalDeformationProjection I =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (Deformation.Iff.BundleCycles.deformationAlgebra ((I.comap i).ideal U)))) ≫
        U.2.fromSpec ≫ i := by
  let a := Spec.map (CommRingCat.ofHom (DeformationDiagram.BundleCycles.openDeformationRingMap i I U))
  let b := Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, (AffineChartBase.BundleCycles.openAffineSiteImage i U).1)
    (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal (AffineChartBase.BundleCycles.openAffineSiteImage i U)))))
  let c := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (Deformation.Iff.BundleCycles.deformationAlgebra ((I.comap i).ideal U))))
  exact (Category.assoc a ((Global.Deformation.BundleCycles.globalDeformationCover I).f (AffineChartBase.BundleCycles.openAffineSiteImage i U))
    (Global.Deformation.BundleCycles.globalDeformationProjection I)).trans
    ((congrArg (fun k => a ≫ k) (Global.PuncturedLaurentChart.BundleCycles.globalDeformationChart_toBase I (AffineChartBase.BundleCycles.openAffineSiteImage i U))).trans
      ((Category.assoc a b (AffineChartBase.BundleCycles.openAffineSiteImage i U).2.fromSpec).symm.trans
        ((congrArg (fun k => k ≫ (AffineChartBase.BundleCycles.openAffineSiteImage i U).2.fromSpec)
          (openDeformationChart_baseSquare i I U)).trans
          ((Category.assoc c (Spec.map (i.appIso U.1).hom) (AffineChartBase.BundleCycles.openAffineSiteImage i U).2.fromSpec).trans
            (congrArg (fun k => c ≫ k) (AffineChartBase.BundleCycles.openAffineSiteImage_fromSpec i U))))))

theorem openDeformationChart_opensRange :
    (openDeformationChart i I U).opensRange =
      Global.Deformation.BundleCycles.globalDeformationProjection I ⁻¹ᵁ (i ''ᵁ U.1) := by
  exact (@Scheme.Hom.opensRange_comp_of_isIso _ _ _
    (Spec.map (CommRingCat.ofHom (DeformationDiagram.BundleCycles.openDeformationRingMap i I U)))
    ((Global.Deformation.BundleCycles.globalDeformationCover I).f (AffineChartBase.BundleCycles.openAffineSiteImage i U))
    (openDeformationChartMap_isIso i I U) ((Global.Deformation.BundleCycles.globalDeformationCover I).map_prop _)).trans
    (Global.DeformationProperties.BundleCycles.globalDeformationProjection_preimage I (AffineChartBase.BundleCycles.openAffineSiteImage i U)).symm

end

section

/-! Deformation along an actual open immersion is the cartesian restriction of the original deformation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (I : Y.IdealSheafData)

theorem openDeformationChart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((Global.Deformation.BundleCycles.deformationGlueData (I.comap i)).natTrans.app U)
      (openDeformationChart i I U) (U.1.ι ≫ i) (Global.Deformation.BundleCycles.globalDeformationProjection I) := by
  apply @IsOpenImmersion.isPullback _ _ _ _
    ((Global.Deformation.BundleCycles.deformationGlueData (I.comap i)).natTrans.app U)
    (openDeformationChart i I U) (U.1.ι ≫ i) (Global.Deformation.BundleCycles.globalDeformationProjection I)
    (openDeformationChart_open i I U) (@IsOpenImmersion.comp _ _ _ U.1.ι i inferInstance inferInstance)
  · exact (openDeformationChart_toBase i I U).trans (Category.assoc _ _ _).symm
  · have h := (Scheme.Hom.opensRange_comp U.1.ι i).trans
      (congrArg (fun V => i ''ᵁ V) U.1.opensRange_ι)
    exact (congrArg (fun V => Global.Deformation.BundleCycles.globalDeformationProjection I ⁻¹ᵁ V) h).trans
      (openDeformationChart_opensRange i I U).symm

theorem globalOpenDeformationMap_isPullback :
    IsPullback (Global.Deformation.BundleCycles.globalDeformationProjection (I.comap i)) (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I)
      i (Global.Deformation.BundleCycles.globalDeformationProjection I) := by
  apply QuotientFiber.BundleCycles.isPullback_of_cover_squares (Global.Deformation.BundleCycles.globalDeformationProjection (I.comap i))
    (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I) i (Global.Deformation.BundleCycles.globalDeformationProjection I) (directedCover X)
    (Global.Deformation.BundleCycles.globalDeformationCover (I.comap i)).X (Global.Deformation.BundleCycles.globalDeformationCover (I.comap i)).f
    (fun U => (Global.Deformation.BundleCycles.deformationGlueData (I.comap i)).natTrans.app U)
    (Global.Deformation.BundleCycles.globalDeformation_chart_isPullback (I.comap i))
  intro U
  have h := openDeformationChart_isPullback i I U
  have he := Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap_on_chart i I U
  exact (congrArg (fun b : (Global.Deformation.BundleCycles.globalDeformationCover (I.comap i)).X U ⟶ Global.Deformation.BundleCycles.globalDeformation I =>
    IsPullback ((Global.Deformation.BundleCycles.deformationGlueData (I.comap i)).natTrans.app U) b
      (U.1.ι ≫ i) (Global.Deformation.BundleCycles.globalDeformationProjection I)) he).mpr h

instance globalOpenDeformationMap_open : IsOpenImmersion (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I) :=
  MorphismProperty.of_isPullback (globalOpenDeformationMap_isPullback i I) inferInstance

theorem globalOpenDeformationMap_toBase :
    Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I ≫ Global.Deformation.BundleCycles.globalDeformationProjection I =
      Global.Deformation.BundleCycles.globalDeformationProjection (I.comap i) ≫ i :=
  (globalOpenDeformationMap_isPullback i I).w.symm

theorem globalOpenDeformationMap_range :
    Set.range (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I) =
      Global.Deformation.BundleCycles.globalDeformationProjection I ⁻¹' Set.range i := by
  have h := Scheme.image_preimage_eq_of_isPullback (globalOpenDeformationMap_isPullback i I) Set.univ
  simpa only [Set.preimage_univ, Set.image_univ] using h

end

/-! The actual global deformation map of an open immersion preserves the parameter morphism and its global section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (I : Y.IdealSheafData)

theorem openDeformationChart_parameter (U : X.AffineZariskiSite) :
    openDeformationChart i I U ≫ Deformation.Parameter.BundleCycles.globalDeformationParameter I =
      Spec.map (CommRingCat.ofHom (Deformation.Parameter.BundleCycles.deformationParameterRingMap ((I.comap i).ideal U))) := by
  let a := Spec.map (CommRingCat.ofHom (DeformationDiagram.BundleCycles.openDeformationRingMap i I U))
  have hr : CommRingCat.ofHom (Deformation.Parameter.BundleCycles.deformationParameterRingMap (I.ideal (AffineChartBase.BundleCycles.openAffineSiteImage i U))) ≫
      CommRingCat.ofHom (DeformationDiagram.BundleCycles.openDeformationRingMap i I U) =
      CommRingCat.ofHom (Deformation.Parameter.BundleCycles.deformationParameterRingMap ((I.comap i).ideal U)) := by
    apply CommRingCat.hom_ext
    exact Deformation.Parameter.BundleCycles.deformationParameterRingMap_natural _ _ _
      (Ideal.map_le_iff_le_comap.mp (AffineChartBase.BundleCycles.openAffineSiteImage_ideal i I U).symm.le)
  exact (Category.assoc a ((Global.Deformation.BundleCycles.globalDeformationCover I).f (AffineChartBase.BundleCycles.openAffineSiteImage i U))
    (Deformation.Parameter.BundleCycles.globalDeformationParameter I)).trans
    ((congrArg (fun k => a ≫ k) (Deformation.Parameter.BundleCycles.globalDeformationParameter_on_chart I (AffineChartBase.BundleCycles.openAffineSiteImage i U))).trans
      ((Spec.map_comp _ _).symm.trans (congrArg Spec.map hr)))

theorem globalOpenDeformationMap_parameter :
    Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I ≫ Deformation.Parameter.BundleCycles.globalDeformationParameter I =
      Deformation.Parameter.BundleCycles.globalDeformationParameter (I.comap i) := by
  apply (Global.Deformation.BundleCycles.globalDeformationCover (I.comap i)).hom_ext
  intro U
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ Deformation.Parameter.BundleCycles.globalDeformationParameter I)
      (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap_on_chart i I U)).trans
      ((openDeformationChart_parameter i I U).trans
        (Deformation.Parameter.BundleCycles.globalDeformationParameter_on_chart (I.comap i) U).symm))

theorem globalOpenDeformationMap_parameterSection :
    (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I).appTop (Global.Specialization.BundleCycles.globalDeformationParameterSection I) =
      Global.Specialization.BundleCycles.globalDeformationParameterSection (I.comap i) :=
  congrArg (fun k => k.appTop Global.Specialization.BundleCycles.parameterLineSection) (globalOpenDeformationMap_parameter i I)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationTo.BundleCycles
