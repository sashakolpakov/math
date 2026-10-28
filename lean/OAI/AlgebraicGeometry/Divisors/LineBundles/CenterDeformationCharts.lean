import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CenterDeformation

/-! # Center Deformation Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.CenterDeformationCharts.BundleCycles

noncomputable section

/-! The polynomial charts of the center deformation give an actual
open cover of the affine line over the center. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem centerLineBaseChart_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion (AffineSpace.map PUnit (Support.Projection.BundleCycles.supportCoefficientChart I U)) :=
  MorphismProperty.of_isPullback (AffineSpace.isPullback_map (n := PUnit) (Support.Projection.BundleCycles.supportCoefficientChart I U)).flip
    (Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion I U)

instance centerDeformationLineChart_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion (Global.CenterDeformation.BundleCycles.centerDeformationLineChart I U) := by
  let : IsOpenImmersion (AffineSpace.map PUnit (Support.Projection.BundleCycles.supportCoefficientChart I U)) :=
    centerLineBaseChart_isOpenImmersion I U
  change IsOpenImmersion ((SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso (I.ideal U)).hom ≫
    AffineSpace.map PUnit (Support.Projection.BundleCycles.supportCoefficientChart I U))
  exact @IsOpenImmersion.comp _ _ _ (SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso (I.ideal U)).hom
    (AffineSpace.map PUnit (Support.Projection.BundleCycles.supportCoefficientChart I U)) inferInstance
    (centerLineBaseChart_isOpenImmersion I U)

theorem centerLineBaseChart_range (U : X.AffineZariskiSite) :
    Set.range (AffineSpace.map PUnit (Support.Projection.BundleCycles.supportCoefficientChart I U)) =
      AffineLine.Charts.BundleCycles.affineLineProjection I.subscheme ⁻¹' Set.range (Support.Projection.BundleCycles.supportCoefficientChart I U) := by
  have h := Scheme.image_preimage_eq_of_isPullback
    (AffineSpace.isPullback_map (n := PUnit) (Support.Projection.BundleCycles.supportCoefficientChart I U)).flip Set.univ
  simpa only [Set.preimage_univ, Set.image_univ, AffineLine.Charts.BundleCycles.affineLineProjection] using h

theorem centerDeformationLineChart_range (U : X.AffineZariskiSite) :
    Set.range (Global.CenterDeformation.BundleCycles.centerDeformationLineChart I U) =
      AffineLine.Charts.BundleCycles.affineLineProjection I.subscheme ⁻¹' Set.range (Support.Projection.BundleCycles.supportCoefficientChart I U) := by
  have hs : Function.Surjective (SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso (I.ideal U)).hom :=
    (SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso (I.ideal U)).hom.homeomorph.surjective
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    apply (congrArg (fun S => Global.CenterDeformation.BundleCycles.centerDeformationLineChart I U a ∈ S)
      (centerLineBaseChart_range I U)).mp
    exact ⟨(SelfSupportDeformation.BundleCycles.selfSupportDeformationLineIso (I.ideal U)).hom a, rfl⟩
  · intro hz
    have hz' : z ∈ Set.range (AffineSpace.map PUnit (Support.Projection.BundleCycles.supportCoefficientChart I U)) :=
      (congrArg (fun S => z ∈ S) (centerLineBaseChart_range I U)).mpr hz
    obtain ⟨a, ha⟩ := hz'
    obtain ⟨b, hb⟩ := hs a
    exact ⟨b, (congrArg (AffineSpace.map PUnit (Support.Projection.BundleCycles.supportCoefficientChart I U)) hb).trans ha⟩

theorem centerDeformationLineChart_covers (x : AffineLine.Charts.BundleCycles.affineLine I.subscheme) :
    ∃ U : X.AffineZariskiSite, x ∈ Set.range (Global.CenterDeformation.BundleCycles.centerDeformationLineChart I U) := by
  obtain ⟨U, u, hu⟩ := I.subschemeCover.openCover.exists_eq (AffineLine.Charts.BundleCycles.affineLineProjection I.subscheme x)
  refine ⟨U, ?_⟩
  rw [centerDeformationLineChart_range I U]
  exact ⟨u, hu⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.CenterDeformationCharts.BundleCycles
