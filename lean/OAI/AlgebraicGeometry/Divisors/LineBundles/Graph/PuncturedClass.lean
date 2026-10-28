import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.IntegralDeformation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.ProductCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedOpenClass

/-! # Punctured Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.PuncturedClass.BundleCycles

noncomputable section

/-! The punctured graph deformation has the native integral, smooth, and metrizable geometry used by the canonical cycle class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

instance graphAmbientOver_smooth : Smooth (Conormal.BundleCycles.graphAmbientOver f).hom := by
  change Smooth (Chow.BundleCycles.graphAmbientStructureMap f)
  rw [← Chow.BundleCycles.graphAmbientStructureMap_first]
  infer_instance

instance graphAmbientOver_finiteType : LocallyOfFiniteType (Conormal.BundleCycles.graphAmbientOver f).hom :=
  Chow.BundleCycles.graphAmbientStructureMap_locallyOfFiniteType f

instance graphAmbientOver_noetherian : AlgebraicGeometry.IsNoetherian (Conormal.BundleCycles.graphAmbientOver f).left :=
  inferInstanceAs (AlgebraicGeometry.IsNoetherian (OpenAmbient.BundleCycles.graphAmbient f))

instance graphPuncturedInclusionOver_open : IsOpenImmersion (CenterEndpointFibers.BundleCycles.graphPuncturedInclusionOver f).left :=
  Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion_isOpenImmersion (OpenAmbient.BundleCycles.graph f).ker

instance graphPuncturedOver_integral [IsIntegral X.carrier] [IsIntegral Y.carrier] :
    IsIntegral (CenterEndpointFibers.BundleCycles.graphPuncturedOver f).left :=
  inferInstanceAs (IsIntegral (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured (OpenAmbient.BundleCycles.graph f).ker))

instance graphPuncturedOver_noetherian : AlgebraicGeometry.IsNoetherian (CenterEndpointFibers.BundleCycles.graphPuncturedOver f).left :=
  inferInstanceAs (AlgebraicGeometry.IsNoetherian (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured (OpenAmbient.BundleCycles.graph f).ker))

instance graphPuncturedOver_smooth : Smooth (CenterEndpointFibers.BundleCycles.graphPuncturedOver f).hom := by
  change Smooth (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker ≫ (DeformationTopology.BundleCycles.graphDeformationOver f).hom)
  exact @smooth_comp _ _ (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (OpenAmbient.BundleCycles.graph f).ker)
    _ (DeformationTopology.BundleCycles.graphDeformationOver f).hom inferInstance (DeformationTopology.BundleCycles.graphDeformationOver_smooth f)

instance graphPuncturedOver_metrizable : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CenterEndpointFibers.BundleCycles.graphPuncturedOver f)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (CenterEndpointFibers.BundleCycles.graphPuncturedInclusionOver f)).isEmbedding.metrizableSpace

def graphPuncturedProjectionOver : CenterEndpointFibers.BundleCycles.graphPuncturedOver f ⟶ Conormal.BundleCycles.graphAmbientOver f :=
  Punctured.ProductCharts.BundleCycles.puncturedProjectionOver (Conormal.BundleCycles.graphAmbientOver f) (OpenAmbient.BundleCycles.graph f).ker

theorem graphPuncturedOneOver_projection :
    DeformationOneBetti.BundleCycles.graphPuncturedOneOver f ≫ graphPuncturedProjectionOver f = 𝟙 (Conormal.BundleCycles.graphAmbientOver f) :=
  Over.OverMorphism.ext (Global.DeformationOneFiber.BundleCycles.globalDeformationOnePunctured_projection (OpenAmbient.BundleCycles.graph f).ker)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.PuncturedClass.BundleCycles
