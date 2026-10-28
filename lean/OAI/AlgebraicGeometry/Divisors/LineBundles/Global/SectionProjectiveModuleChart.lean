import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SectionAffineSpaceCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectiveProper

/-! # Section Projective Module Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SectionProjectiveModuleChart.BundleCycles

noncomputable section

section

/-! Target-local properties of augmented projective conormal charts
give the same property for the actual compactification of a smooth closed section. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (P : MorphismProperty Scheme.{0})
    (hP : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
      [Module.Projective R M] [Module.Finite R M], P (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)))
    {X Y : Scheme.{0}} (p : Y ⟶ X) [Smooth p]
    (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)

include hP hs in
theorem globalSection_projective_property_pointChart (z : s.ker.subscheme) :
    ∃ U : Y.AffineZariskiSite, z ∈ (Support.Projection.BundleCycles.supportCoefficientChart s.ker U).opensRange ∧
      P ((Conormal.ProjectiveGluing.BundleCycles.conormalProjectiveToCoefficients s.ker).app U) := by
  obtain ⟨x, rfl⟩ := (Scheme.homeoOfIso (asIso s.toImage)).surjective z
  obtain ⟨U, V, hU, hV, hx, hVU, hUV⟩ := Section.AffineNeighborhoodInside.BundleCycles.section_exists_affineNeighborhoods p s hs x
  let W : Y.AffineZariskiSite := ⟨U, hU⟩
  obtain ⟨hfinite, hprojective⟩ := Affine.SectionChartConormal.BundleCycles.affineSectionChart_conormal_finite_projective p s hs U V hU hV hVU hUV
  have hz : s.toImage x ∈ (Support.Projection.BundleCycles.supportCoefficientChart s.ker W).opensRange := by
    rw [Support.Projection.BundleCycles.supportCoefficientChart_range]
    have he : s.ker.subschemeι (s.toImage x) = s x := congrArg (fun f => f x) s.toImage_imageι
    change s.ker.subschemeι (s.toImage x) ∈ U
    rw [he]
    exact hVU hx
  refine ⟨W, hz, ?_⟩
  exact @hP (Γ(Y, U) ⧸ s.ker.ideal W) (s.ker.ideal W).Cotangent
    inferInstance inferInstance inferInstance hprojective hfinite

include hP hs in
theorem globalSection_projective_property [IsZariskiLocalAtTarget P] :
    P (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker) := by
  choose U hx hU using globalSection_projective_property_pointChart P hP p s hs
  let C : s.ker.subscheme.OpenCover := Scheme.Cover.mkOfCovers _
    (fun z => Spec (.of (Γ(Y, (U z).1) ⧸ s.ker.ideal (U z))))
    (fun z => Support.Projection.BundleCycles.supportCoefficientChart s.ker (U z)) (fun z => ⟨z, hx z⟩)
    (fun z => Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion s.ker (U z))
  exact DeformationProperties.BundleCycles.morphismProperty_of_cover_pullbacks P (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker) C
    (fun z => Conormal.ProjectiveDiagram.BundleCycles.conormalProjectiveChart s.ker (U z))
    (fun z => (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover s.ker).f (U z))
    (fun z => (Conormal.ProjectiveGluing.BundleCycles.conormalProjectiveToCoefficients s.ker).app (U z))
    (fun z => Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport_chart_isPullback s.ker (U z)) hU

end

/-! Every point of a smooth closed section lies in an actual
conormal coefficient chart with a finite projective module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (p : Y ⟶ X) [Smooth p]
    (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)

include p hs in
theorem globalSection_exists_projectiveModuleChart (z : s.ker.subscheme) :
    ∃ U : Y.AffineZariskiSite, z ∈ (Support.Projection.BundleCycles.supportCoefficientChart s.ker U).opensRange ∧
      Module.Finite (Γ(Y, U.1) ⧸ s.ker.ideal U) (s.ker.ideal U).Cotangent ∧
      Module.Projective (Γ(Y, U.1) ⧸ s.ker.ideal U) (s.ker.ideal U).Cotangent := by
  obtain ⟨x, rfl⟩ := (Scheme.homeoOfIso (asIso s.toImage)).surjective z
  obtain ⟨U, V, hU, hV, hx, hVU, hUV⟩ := Section.AffineNeighborhoodInside.BundleCycles.section_exists_affineNeighborhoods p s hs x
  let W : Y.AffineZariskiSite := ⟨U, hU⟩
  obtain ⟨hfinite, hprojective⟩ := Affine.SectionChartConormal.BundleCycles.affineSectionChart_conormal_finite_projective p s hs U V hU hV hVU hUV
  refine ⟨W, ?_, hfinite, hprojective⟩
  rw [Support.Projection.BundleCycles.supportCoefficientChart_range]
  have he : s.ker.subschemeι (s.toImage x) = s x := congrArg (fun f => f x) s.toImage_imageι
  change s.ker.subschemeι (s.toImage x) ∈ U
  rw [he]
  exact hVU hx

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SectionProjectiveModuleChart.BundleCycles
