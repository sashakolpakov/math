import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.DeformationChartSmooth
import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.ProjectionSmooth
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.OpenNeighborhoods
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Conormal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.AffineNeighborhoodInside

/-! # Deformation Smooth -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationSmooth.BundleCycles

noncomputable section

/-! The actual global deformation of the graph is smooth over its source.
This follows from genuine section charts at the special fiber and Laurent
charts on the punctured deformation, for every morphism of presentations. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphDeformationToSource : Global.Deformation.BundleCycles.globalDeformation (OpenAmbient.BundleCycles.graph f).ker ⟶ X.carrier :=
  Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker ≫ OpenAmbient.BundleCycles.graphFirstProjection f

instance graphDeformationToSource_smooth : Smooth (graphDeformationToSource f) := by
  apply LineBundles.Smooth.OpenNeighborhoods.BundleCycles.smooth_of_open_neighborhoods
  intro x
  by_cases hx : x ∈ Set.range (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker)
  · obtain ⟨U, u, hu⟩ := (Global.Deformation.BundleCycles.globalDeformationCover (OpenAmbient.BundleCycles.graph f).ker).exists_eq x
    let W : (OpenAmbient.BundleCycles.graphAmbient f).AffineZariskiSite := U
    refine ⟨Spec (CommRingCat.of (LaurentPolynomial Γ(OpenAmbient.BundleCycles.graphAmbient f, W.1))),
      Global.PuncturedLaurentChart.BundleCycles.globalPuncturedLaurentChart (OpenAmbient.BundleCycles.graph f).ker W,
      Global.PuncturedLaurentChart.BundleCycles.globalPuncturedLaurentChart_openImmersion (OpenAmbient.BundleCycles.graph f).ker W, ?_, ?_⟩
    · rw [Global.PuncturedLaurentChart.BundleCycles.globalPuncturedLaurentChart_range (OpenAmbient.BundleCycles.graph f).ker W]
      refine ⟨⟨u, hu⟩, ?_⟩
      exact (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen (OpenAmbient.BundleCycles.graph f).ker).range_ι ▸ hx
    · change Smooth (Global.PuncturedLaurentChart.BundleCycles.globalPuncturedLaurentChart (OpenAmbient.BundleCycles.graph f).ker W ≫
        (Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker ≫ OpenAmbient.BundleCycles.graphFirstProjection f))
      rw [← Category.assoc, Global.PuncturedLaurentChart.BundleCycles.globalPuncturedLaurentChart_toBase (OpenAmbient.BundleCycles.graph f).ker W]
      infer_instance
  · have hx' : x ∈ Set.range (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (OpenAmbient.BundleCycles.graph f).ker) := by
      rw [Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured_closed_complement]
      exact hx
    obtain ⟨y, rfl⟩ := hx'
    obtain ⟨U, V, hU, hV, hyV, hVU, hUV⟩ := Section.AffineNeighborhoodInside.BundleCycles.section_exists_affineNeighborhoods
      (OpenAmbient.BundleCycles.graphFirstProjection f) (OpenAmbient.BundleCycles.graph f) (OpenAmbient.BundleCycles.graph_firstProjection f) (Chow.BundleCycles.graphNormalProjection f y)
    let W : (OpenAmbient.BundleCycles.graphAmbient f).AffineZariskiSite := ⟨U, hU⟩
    refine ⟨(Global.Deformation.BundleCycles.globalDeformationCover (OpenAmbient.BundleCycles.graph f).ker).X W,
      (Global.Deformation.BundleCycles.globalDeformationCover (OpenAmbient.BundleCycles.graph f).ker).f W,
      Global.DeformationProperties.BundleCycles.globalDeformationCover_isOpenImmersion (OpenAmbient.BundleCycles.graph f).ker W, ?_, ?_⟩
    · change Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (OpenAmbient.BundleCycles.graph f).ker y ∈
        ((Global.Deformation.BundleCycles.globalDeformationCover (OpenAmbient.BundleCycles.graph f).ker).f W).opensRange
      rw [← Global.DeformationProperties.BundleCycles.globalDeformationProjection_preimage]
      change Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (OpenAmbient.BundleCycles.graph f).ker y) ∈ U
      have he : Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (OpenAmbient.BundleCycles.graph f).ker y) =
          OpenAmbient.BundleCycles.graph f (Chow.BundleCycles.graphNormalProjection f y) :=
        (congrArg (fun k => k y) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase (OpenAmbient.BundleCycles.graph f).ker)).trans
          (congrArg (fun k => k y) (Conormal.BundleCycles.graphNormalProjection_graph f)).symm
      rw [he]
      exact hVU hyV
    · exact Section.DeformationChartSmooth.BundleCycles.sectionDeformationChart_smooth (OpenAmbient.BundleCycles.graphFirstProjection f) (OpenAmbient.BundleCycles.graph f)
        (OpenAmbient.BundleCycles.graph_firstProjection f) U V hU hV hVU hUV

instance graphDeformationStructure_smooth :
    Smooth (Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker ≫ Chow.BundleCycles.graphAmbientStructureMap f) := by
  have he : Global.Deformation.BundleCycles.globalDeformationProjection (OpenAmbient.BundleCycles.graph f).ker ≫ Chow.BundleCycles.graphAmbientStructureMap f =
      graphDeformationToSource f ≫ X.structureMap := by
    rw [graphDeformationToSource, Category.assoc, Chow.BundleCycles.graphAmbientStructureMap_first]
  rw [he]
  infer_instance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationSmooth.BundleCycles
