import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponentPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionPointDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PointComponentDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentRank
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Conormal
import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalSpecializationGrading

/-! # Specialization Point Codimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationPointCodimension.BundleCycles

noncomputable section

/-! The dimension of every point appearing in the specialization of a
graph-projection component, measured in its actual normal-bundle component. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def GraphConePointHasCodimension (p : ℕ) (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker) : Prop :=
  Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) (Chow.BundleCycles.graphConeStructureMap f) + p =
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension
      (X.componentVariety (X.supportComponent (irreducibleSetEquivPoints.symm (Chow.BundleCycles.graphNormalProjection f y)))).structureMap +
    AffineBundle.FiberRank.Cycles.affineBundleFiberRank (Chow.BundleCycles.graphNormalProjection f) X.structureMap (Chow.BundleCycles.graphNormalProjection f y)

theorem graphProjectionSpecialization_point_codimension (C : irreducibleComponents X.carrier)
    (v : Y.carrier) (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker)
    (hy : Global.CycleSpecialization.BundleCycles.globalPrimeSpecializationQ (OpenAmbient.BundleCycles.graph f).ker (ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint f C v) y ≠ 0) :
    GraphConePointHasCodimension f (Y.supportCodimension (irreducibleSetEquivPoints.symm v)) y := by
  let D := Y.supportComponent (irreducibleSetEquivPoints.symm v)
  let : IsClosedImmersion (X.componentInclusion C) := X.componentInclusion_isClosedImmersion C
  let : IsClosedImmersion (Y.componentInclusion D) := Y.componentInclusion_isClosedImmersion D
  have hs := GlobalSpecializationGrading.BundleCycles.globalPrimeSpecializationQ_specializes (OpenAmbient.BundleCycles.graph f).ker
    (ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint f C v) y hy
  have hxC : Chow.BundleCycles.graphNormalProjection f y ∈ Set.range (X.componentInclusion C) :=
    (hs.map (OpenAmbient.BundleCycles.graphFirstProjection f).continuous).mem_closed
      (X.componentInclusion C).isClosedEmbedding.isClosed_range
      (ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint_first_mem f C v)
  have hvD : v ∈ Set.range (Y.componentInclusion D) := Projective.PointComponentDimension.BundleCycles.projectivePoint_mem_supportComponent Y v
  have hxD : f.left (Chow.BundleCycles.graphNormalProjection f y) ∈ Set.range (Y.componentInclusion D) := by
    have H := (hs.map (OpenAmbient.BundleCycles.graphSecondProjection f).continuous).mem_closed
      (Y.componentInclusion D).isClosedEmbedding.isClosed_range
      ((ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint_second f C v).symm ▸ hvD)
    have he := congrArg (fun a => a y) (Conormal.BundleCycles.graphCone_secondProjection f)
    exact he ▸ H
  have hr := GraphNormal.ComponentRank.BundleCycles.graphNormalFiberRank_at_targetComponent f D (Chow.BundleCycles.graphNormalProjection f y) hxD
  have hd := GlobalSpecializationGrading.BundleCycles.globalPrimeSpecializationQ_dimension (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f)
    (ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint f C v) y hy
  have hp := ProjectionPointDimension.BundleCycles.graphProjectionComponentPoint_dimension f C v
  have hv := Projective.PointComponentDimension.BundleCycles.projectiveSupport_dimension_add_codimension Y (irreducibleSetEquivPoints.symm v)
  have hc := congrArg (fun A : irreducibleComponents X.carrier =>
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety A).structureMap)
      (Projective.PointComponentDimension.BundleCycles.projectivePoint_supportComponent X C (Chow.BundleCycles.graphNormalProjection f y) hxC)
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) (Chow.BundleCycles.graphConeStructureMap f) = _ at hd
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint f C v))
    (Chow.BundleCycles.graphAmbientStructureMap f) = _ at hp
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm v) Y.structureMap +
    Y.supportCodimension (irreducibleSetEquivPoints.symm v) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Y.componentVariety D).structureMap at hv
  unfold GraphConePointHasCodimension
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationPointCodimension.BundleCycles
