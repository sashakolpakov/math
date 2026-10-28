import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.PuncturedClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecialFiberSection

/-! # Deformation Dimensions -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationDimensions.BundleCycles

noncomputable section

/-! The actual integral graph ambient and normal fiber have the same dimension; the punctured and full deformations each have one additional dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier] [IsIntegral Y.carrier]
  (f : X.toOver ⟶ Y.toOver)

theorem graphDeformation_dimension :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (DeformationTopology.BundleCycles.graphDeformationOver f).hom =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Conormal.BundleCycles.graphAmbientOver f).hom + 1 :=
  Deformation.Dimension.BundleCycles.globalDeformation_dimension (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f)

theorem graphCone_dimension_eq_ambient :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Conormal.BundleCycles.graphConeOver f).hom =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Conormal.BundleCycles.graphAmbientOver f).hom := by
  have h := SpecialFiberSection.BundleCycles.graphSpecialFiber_nativeCodimension f
  have hX := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension (Conormal.BundleCycles.graphConeOver f).hom
  have hY := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension (DeformationTopology.BundleCycles.graphDeformationOver f).hom
  have hD := graphDeformation_dimension f
  omega

theorem graphPunctured_dimension :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (CenterEndpointFibers.BundleCycles.graphPuncturedOver f).hom =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Conormal.BundleCycles.graphAmbientOver f).hom + 1 :=
  (Open.SupportOver.BundleCycles.openImmersionOver_dimension (CenterEndpointFibers.BundleCycles.graphPuncturedInclusionOver f)).trans (graphDeformation_dimension f)

theorem graphPunctured_codimension (d p : ℕ)
    (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Conormal.BundleCycles.graphAmbientOver f).hom) :
    (d + 1) + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (CenterEndpointFibers.BundleCycles.graphPuncturedOver f).hom := by
  rw [graphPunctured_dimension]
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationDimensions.BundleCycles
