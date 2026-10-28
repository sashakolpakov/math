import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.AffineSpaceChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartConormal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.AffineNeighborhoodInside

/-! # Section Affine Space Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SectionAffineSpaceCharts.BundleCycles

noncomputable section

/-! # LineBundleCycles: affine-space bundle charts for the actual conormal of any smooth closed section -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem globalSection_exists_affineSpaceChart {X Y : Scheme.{0}} (p : Y ⟶ X) [Smooth p]
    (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X) (z : s.ker.subscheme) :
    ∃ (B : CommRingCat.{0}) (i : Spec B ⟶ s.ker.subscheme) (ι : Type) (_ : Finite ι)
      (j : AffineSpace ι (Spec B) ⟶ Conormal.DiagramGluing.BundleCycles.globalConormalSpectrum s.ker),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧ z ∈ Set.range i ∧
      IsPullback (AffineSpace ι (Spec B) ↘ Spec B) j i (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) := by
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
  obtain ⟨q, hq⟩ := hz
  obtain ⟨B, i, ι, hι, j, hi, hj, hz', hsq⟩ :=
    @Conormal.AffineSpaceChart.BundleCycles.conormal_exists_affineSpaceChart Y s.ker W hprojective hfinite q
  exact ⟨B, i, ι, hι, j, hi, hj, hq ▸ hz', hsq⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SectionAffineSpaceCharts.BundleCycles
