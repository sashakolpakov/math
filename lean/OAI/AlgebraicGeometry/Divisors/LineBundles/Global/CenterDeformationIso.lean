import OAI.AlgebraicGeometry.Divisors.LineBundles.CenterDeformationCharts
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenAmbient

/-! # Center Deformation Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CenterDeformationIso.BundleCycles

noncomputable section

section

/-! The center's actual self-deformation is the affine line over the
center. Injectivity and surjectivity are proved on the constructed charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem globalCenterDeformationToLine_injective : Function.Injective (CenterDeformation.BundleCycles.globalCenterDeformationToLine I) := by
  intro x y hxy
  have hb : Support.Projection.BundleCycles.globalSupportDeformationToSupport I I x = Support.Projection.BundleCycles.globalSupportDeformationToSupport I I y :=
    (congrArg (fun k => k x) (CenterDeformation.BundleCycles.globalCenterDeformationToLine_over I)).symm.trans
      ((congrArg (AffineLine.Charts.BundleCycles.affineLineProjection I.subscheme) hxy).trans
        (congrArg (fun k => k y) (CenterDeformation.BundleCycles.globalCenterDeformationToLine_over I)))
  obtain ⟨U, u, hu⟩ := (SupportDeformation.BundleCycles.globalSupportDeformationCover I I).exists_eq x
  let W : X.AffineZariskiSite := U
  have hxW : x ∈ ((SupportDeformation.BundleCycles.globalSupportDeformationCover I I).f W).opensRange := ⟨u, hu⟩
  have hyW : y ∈ ((SupportDeformation.BundleCycles.globalSupportDeformationCover I I).f W).opensRange := by
    rw [← Support.Projection.BundleCycles.globalSupportDeformationToSupport_preimage I I W] at hxW ⊢
    change Support.Projection.BundleCycles.globalSupportDeformationToSupport I I y ∈ (Support.Projection.BundleCycles.supportCoefficientChart I W).opensRange
    exact hb ▸ hxW
  obtain ⟨v, hv⟩ := hyW
  have he (z : (SupportDeformation.BundleCycles.globalSupportDeformationCover I I).X W) :
      CenterDeformation.BundleCycles.globalCenterDeformationToLine I ((SupportDeformation.BundleCycles.globalSupportDeformationCover I I).f W z) =
        CenterDeformation.BundleCycles.centerDeformationLineChart I W z :=
    congrArg (fun k => k z) (CenterDeformation.BundleCycles.globalCenterDeformationToLine_on_chart I W)
  have huv : u = v := (CenterDeformation.BundleCycles.centerDeformationLineChart I W).isOpenEmbedding.injective
    ((he u).symm.trans ((congrArg (CenterDeformation.BundleCycles.globalCenterDeformationToLine I) hu).trans
      (hxy.trans ((congrArg (CenterDeformation.BundleCycles.globalCenterDeformationToLine I) hv).symm.trans (he v)))))
  exact hu.symm.trans ((congrArg ((SupportDeformation.BundleCycles.globalSupportDeformationCover I I).f W) huv).trans hv)

instance globalCenterDeformationToLine_isOpenImmersion : IsOpenImmersion (CenterDeformation.BundleCycles.globalCenterDeformationToLine I) := by
  apply IsOpenImmersion.of_openCover_source (CenterDeformation.BundleCycles.globalCenterDeformationToLine I)
    (SupportDeformation.BundleCycles.globalSupportDeformationCover I I) (globalCenterDeformationToLine_injective I)
  intro U
  exact (congrArg (fun k => IsOpenImmersion k) (CenterDeformation.BundleCycles.globalCenterDeformationToLine_on_chart I U)).mpr
    (CenterDeformationCharts.BundleCycles.centerDeformationLineChart_isOpenImmersion I U)

theorem globalCenterDeformationToLine_surjective : Function.Surjective (CenterDeformation.BundleCycles.globalCenterDeformationToLine I) := by
  intro x
  obtain ⟨U, y, hy⟩ := CenterDeformationCharts.BundleCycles.centerDeformationLineChart_covers I x
  refine ⟨(SupportDeformation.BundleCycles.globalSupportDeformationCover I I).f U y, ?_⟩
  exact (congrArg (fun k => k y) (CenterDeformation.BundleCycles.globalCenterDeformationToLine_on_chart I U)).trans hy

instance globalCenterDeformationToLine_isIso : IsIso (CenterDeformation.BundleCycles.globalCenterDeformationToLine I) :=
  (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨inferInstance, ⟨globalCenterDeformationToLine_surjective I⟩⟩

def globalCenterDeformationLineIso : SupportDeformation.BundleCycles.globalSupportDeformation I I ≅ AffineLine.Charts.BundleCycles.affineLine I.subscheme :=
  asIso (CenterDeformation.BundleCycles.globalCenterDeformationToLine I)

end

/-! The actual constant center family inside the global deformation,
and its specialization to the graph of an arbitrary morphism. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def globalCenterFamily : AffineLine.Charts.BundleCycles.affineLine I.subscheme ⟶ Deformation.BundleCycles.globalDeformation I :=
  (globalCenterDeformationLineIso I).inv ≫ SupportDeformation.BundleCycles.globalSupportDeformationMap I I

theorem globalCenterDeformationLineIso_inv_over :
    (globalCenterDeformationLineIso I).inv ≫ Support.Projection.BundleCycles.globalSupportDeformationToSupport I I =
      AffineLine.Charts.BundleCycles.affineLineProjection I.subscheme := by
  rw [← CenterDeformation.BundleCycles.globalCenterDeformationToLine_over]
  change (globalCenterDeformationLineIso I).inv ≫
    ((globalCenterDeformationLineIso I).hom ≫ AffineLine.Charts.BundleCycles.affineLineProjection I.subscheme) = _
  rw [Iso.inv_hom_id_assoc]

theorem globalCenterFamily_toBase :
    globalCenterFamily I ≫ Deformation.BundleCycles.globalDeformationProjection I =
      AffineLine.Charts.BundleCycles.affineLineProjection I.subscheme ≫ I.subschemeι := by
  change ((globalCenterDeformationLineIso I).inv ≫ SupportDeformation.BundleCycles.globalSupportDeformationMap I I) ≫ _ = _
  rw [Category.assoc, SupportDeformation.BundleCycles.globalSupportDeformationMap_toBase,
    ← Support.Projection.BundleCycles.globalSupportDeformationToSupport_toBase, ← Category.assoc, globalCenterDeformationLineIso_inv_over]

def graphCenterFamily {P Q : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : P.toOver ⟶ Q.toOver) :
    AffineLine.Charts.BundleCycles.affineLine P.carrier ⟶ Deformation.BundleCycles.globalDeformation (Graph.OpenAmbient.BundleCycles.graph f).ker :=
  AffineSpace.map PUnit (Graph.OpenAmbient.BundleCycles.graph f).toImage ≫ globalCenterFamily (Graph.OpenAmbient.BundleCycles.graph f).ker

theorem graphCenterFamily_toBase {P Q : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : P.toOver ⟶ Q.toOver) :
    graphCenterFamily f ≫ Deformation.BundleCycles.globalDeformationProjection (Graph.OpenAmbient.BundleCycles.graph f).ker =
      AffineLine.Charts.BundleCycles.affineLineProjection P.carrier ≫ Graph.OpenAmbient.BundleCycles.graph f := by
  change (AffineSpace.map PUnit (Graph.OpenAmbient.BundleCycles.graph f).toImage ≫ globalCenterFamily (Graph.OpenAmbient.BundleCycles.graph f).ker) ≫ _ = _
  rw [Category.assoc, globalCenterFamily_toBase, ← Category.assoc]
  have hm : AffineSpace.map PUnit (Graph.OpenAmbient.BundleCycles.graph f).toImage ≫ AffineLine.Charts.BundleCycles.affineLineProjection (Graph.OpenAmbient.BundleCycles.graph f).ker.subscheme =
      AffineLine.Charts.BundleCycles.affineLineProjection P.carrier ≫ (Graph.OpenAmbient.BundleCycles.graph f).toImage := AffineSpace.map_over (Graph.OpenAmbient.BundleCycles.graph f).toImage
  rw [hm, Category.assoc, Scheme.Hom.toImage_imageι]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CenterDeformationIso.BundleCycles
