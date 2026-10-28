import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.AffineNeighborhoodInside
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartCone
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SupportCover
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.NormalConeEmbedding
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineIsomorphism
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenAmbient

/-! # Graph Normal Cone -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.GraphNormalCone.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: the actual global normal cone of a smooth closed section is its conormal spectrum -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

theorem globalSection_normalConeToConormal_isIso {X Y : Scheme.{0}} (p : Y ⟶ X) [Smooth p]
    (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X) :
    IsIso (NormalConeEmbedding.BundleCycles.globalNormalConeToConormal s.ker) := by
  choose U V hU hV hx hVU hUV using Section.AffineNeighborhoodInside.BundleCycles.section_exists_affineNeighborhoods p s hs
  let W : X → Y.AffineZariskiSite := fun x => ⟨U x, hU x⟩
  have hW : ∀ z : s.ker.subscheme, ∃ x, s.ker.subschemeι z ∈ (W x).1 := by
    intro z
    obtain ⟨x, rfl⟩ := (Scheme.homeoOfIso (asIso s.toImage)).surjective z
    refine ⟨x, ?_⟩
    have he : s.ker.subschemeι (s.toImage x) = s x := congrArg (fun f => f x) s.toImage_imageι
    change s.ker.subschemeι (s.toImage x) ∈ U x
    rw [he]
    exact hVU x (hx x)
  let C := Conormal.SupportCover.BundleCycles.conormalSupportCover s.ker W hW
  apply Relative.AffineIsomorphism.BundleCycles.isIso_of_cover_pullbacks (NormalConeEmbedding.BundleCycles.globalNormalConeToConormal s.ker) C
    (fun x => (SpecialFiber.BundleCycles.globalSpecialFiberCover s.ker).X (W x))
    (fun x => (SpecialFiber.BundleCycles.globalSpecialFiberCover s.ker).f (W x))
    (fun x => Spec.map ((Conormal.SymmetricDiagram.BundleCycles.conormalSymmetricToSpecialDiagram s.ker).app (.op (W x))))
    (fun x => NormalConeEmbedding.BundleCycles.globalNormalConeToConormal_chart_isPullback s.ker (W x))
  intro x
  apply isIso_SpecMap_iff.mpr
  exact (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv (s.ker.ideal (W x))).bijective.comp
    (Affine.SectionChartCone.BundleCycles.affineSectionChart_normalCone_bijective p s hs (U x) (V x) (hU x) (hV x) (hVU x) (hUV x))

end

/-! # LineBundleCycles: the actual global graph normal cone is its conormal symmetric spectrum -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

instance graphNormalConeToConormal_isIso : IsIso (NormalConeEmbedding.BundleCycles.globalNormalConeToConormal (Graph.OpenAmbient.BundleCycles.graph f).ker) :=
  globalSection_normalConeToConormal_isIso (Graph.OpenAmbient.BundleCycles.graphFirstProjection f) (Graph.OpenAmbient.BundleCycles.graph f) (Graph.OpenAmbient.BundleCycles.graph_firstProjection f)

def graphNormalConeEquiv : SpecialFiber.BundleCycles.globalSpecialFiber (Graph.OpenAmbient.BundleCycles.graph f).ker ≅ Conormal.DiagramGluing.BundleCycles.globalConormalSpectrum (Graph.OpenAmbient.BundleCycles.graph f).ker :=
  asIso (NormalConeEmbedding.BundleCycles.globalNormalConeToConormal (Graph.OpenAmbient.BundleCycles.graph f).ker)

def graphConormalProjection : Conormal.DiagramGluing.BundleCycles.globalConormalSpectrum (Graph.OpenAmbient.BundleCycles.graph f).ker ⟶ X.carrier :=
  Conormal.DiagramGluing.BundleCycles.globalConormalSpectrumProjection (Graph.OpenAmbient.BundleCycles.graph f).ker ≫ Graph.OpenAmbient.BundleCycles.graphFirstProjection f

theorem graphNormalConeEquiv_toSource :
    (graphNormalConeEquiv f).hom ≫ graphConormalProjection f =
      SpecialFiber.BundleCycles.globalSpecialFiberProjection (Graph.OpenAmbient.BundleCycles.graph f).ker ≫ Graph.OpenAmbient.BundleCycles.graphFirstProjection f := by
  change NormalConeEmbedding.BundleCycles.globalNormalConeToConormal (Graph.OpenAmbient.BundleCycles.graph f).ker ≫
    (Conormal.DiagramGluing.BundleCycles.globalConormalSpectrumProjection (Graph.OpenAmbient.BundleCycles.graph f).ker ≫ Graph.OpenAmbient.BundleCycles.graphFirstProjection f) = _
  rw [← Category.assoc, NormalConeEmbedding.BundleCycles.globalNormalConeToConormal_toBase]

theorem graphConormalProjection_toAmbient :
    graphConormalProjection f ≫ Graph.OpenAmbient.BundleCycles.graph f = Conormal.DiagramGluing.BundleCycles.globalConormalSpectrumProjection (Graph.OpenAmbient.BundleCycles.graph f).ker := by
  have he : (Graph.OpenAmbient.BundleCycles.graph f).imageι ≫ Graph.OpenAmbient.BundleCycles.graphFirstProjection f ≫ Graph.OpenAmbient.BundleCycles.graph f = (Graph.OpenAmbient.BundleCycles.graph f).imageι := by
    apply (cancel_epi (Graph.OpenAmbient.BundleCycles.graph f).toImage).mp
    rw [← Category.assoc, ← Category.assoc, Scheme.Hom.toImage_imageι,
      Graph.OpenAmbient.BundleCycles.graph_firstProjection, Category.id_comp]
  change (Conormal.DiagramGluing.BundleCycles.globalConormalSpectrumProjection (Graph.OpenAmbient.BundleCycles.graph f).ker ≫ Graph.OpenAmbient.BundleCycles.graphFirstProjection f) ≫ Graph.OpenAmbient.BundleCycles.graph f = _
  rw [← Conormal.SupportCover.BundleCycles.globalConormalToSupport_toBase (Graph.OpenAmbient.BundleCycles.graph f).ker, Category.assoc, Category.assoc, he]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.GraphNormalCone.BundleCycles
