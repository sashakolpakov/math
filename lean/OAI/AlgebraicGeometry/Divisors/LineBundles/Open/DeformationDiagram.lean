import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.AffineChartBase
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.MapInjective

/-! # Deformation Diagram -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationDiagram.BundleCycles

noncomputable section

/-! The section isomorphisms of an actual open immersion induce a natural isomorphism on its affine deformation charts, with the pulled-back center ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (I : Y.IdealSheafData)

def openDeformationRingMap (U : X.AffineZariskiSite) :
    Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal (AffineChartBase.BundleCycles.openAffineSiteImage i U)) →+* Deformation.Iff.BundleCycles.deformationAlgebra ((I.comap i).ideal U) :=
  Deformation.Maps.BundleCycles.deformationMap _ _ (i.appIso U.1).hom.hom
    (Ideal.map_le_iff_le_comap.mp (AffineChartBase.BundleCycles.openAffineSiteImage_ideal i I U).symm.le)

theorem openDeformationRingMap_bijective (U : X.AffineZariskiSite) :
    Function.Bijective (openDeformationRingMap i I U) :=
  ⟨Deformation.MapInjective.BundleCycles.deformationMap_injective _ _ _ _ (ConcreteCategory.bijective_of_isIso (i.appIso U.1).hom).1,
    Deformation.ClosedSupport.BundleCycles.deformationMap_surjective _ _ _ (ConcreteCategory.bijective_of_isIso (i.appIso U.1).hom).2
      (AffineChartBase.BundleCycles.openAffineSiteImage_ideal i I U).symm _⟩

def openDeformationDiagramMap :
    (AffineChartBase.BundleCycles.openAffineSiteImageFunctor i).op ⋙ Global.Deformation.BundleCycles.deformationDiagram I ⟶ Global.Deformation.BundleCycles.deformationDiagram (I.comap i) where
  app U := CommRingCat.ofHom (openDeformationRingMap i I U.unop)
  naturality {U V} h := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    apply Subtype.ext
    ext n
    have hc := ConcreteCategory.congr_hom (AffineChartBase.BundleCycles.openAffineSiteImage_sections_naturality i h.unop) (p.val.coeff n)
    change (openDeformationRingMap i I V.unop
      ((Global.Deformation.BundleCycles.deformationDiagram I).map ((AffineChartBase.BundleCycles.openAffineSiteImageFunctor i).op.map h) p)).val.coeff n =
      ((Global.Deformation.BundleCycles.deformationDiagram (I.comap i)).map h (openDeformationRingMap i I U.unop p)).val.coeff n
    dsimp only [openDeformationRingMap, Global.Deformation.BundleCycles.deformationDiagram]
    change (Deformation.Maps.BundleCycles.deformationMap _ _ (i.appIso V.unop.1).hom.hom
      (Ideal.map_le_iff_le_comap.mp (AffineChartBase.BundleCycles.openAffineSiteImage_ideal i I V.unop).symm.le)
      (Deformation.Maps.BundleCycles.deformationMap _ _
        (Y.presheaf.map (homOfLE (i.image_mono (Scheme.AffineZariskiSite.toOpens_mono h.unop.le))).op).hom
        (I.ideal_le_comap_ideal (i.image_mono (Scheme.AffineZariskiSite.toOpens_mono h.unop.le))) p)).val.coeff n =
      (Deformation.Maps.BundleCycles.deformationMap _ _ (X.presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono h.unop.le)).op).hom
        ((I.comap i).ideal_le_comap_ideal (Scheme.AffineZariskiSite.toOpens_mono h.unop.le))
        (Deformation.Maps.BundleCycles.deformationMap _ _ (i.appIso U.unop.1).hom.hom
          (Ideal.map_le_iff_le_comap.mp (AffineChartBase.BundleCycles.openAffineSiteImage_ideal i I U.unop).symm.le) p)).val.coeff n
    exact ((Deformation.Maps.BundleCycles.deformationMap_coeff _ _ _ _ _ n).trans
      (congrArg _ (Deformation.Maps.BundleCycles.deformationMap_coeff _ _ _ _ _ n))).trans
      (hc.trans ((Deformation.Maps.BundleCycles.deformationMap_coeff _ _ _ _ _ n).trans
        (congrArg _ (Deformation.Maps.BundleCycles.deformationMap_coeff _ _ _ _ _ n))).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationDiagram.BundleCycles
