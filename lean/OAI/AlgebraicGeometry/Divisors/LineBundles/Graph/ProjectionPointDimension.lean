import OAI.AlgebraicGeometry.Divisors.LineBundles.ProductFiberSupportDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponents

/-! # Projection Point Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionPointDimension.BundleCycles

noncomputable section

/-! Each component of the actual graph projection adds exactly the
source component dimension to a point's support dimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

theorem graphProjectionComponentFiberGeneric_dimension (C : irreducibleComponents X.carrier) (y : Y.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension
        (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (ProjectionComponents.BundleCycles.graphProjectionComponentMap f C) y))
        (ProjectionComponents.BundleCycles.graphProjectionComponentMap f C ≫ Y.structureMap) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety C).structureMap +
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) Y.structureMap := by
  let A := Over.mk (X.componentInclusion C ≫ (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap))
  have hb : A.hom = (X.componentVariety C).structureMap := by
    change X.componentInclusion C ≫ (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap) = _
    have hf : (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap) = X.structureMap := f.w
    rw [hf, X.componentInclusion_over]
  let : IsIntegral A.left := inferInstanceAs (IsIntegral (X.componentVariety C).carrier)
  let : LocallyOfFiniteType A.hom := hb.symm ▸ inferInstance
  let : Smooth A.hom := by
    rw [hb, ← X.componentInclusion_over C]
    let : IsOpenImmersion (X.componentInclusion C) := X.componentInclusion_isOpenImmersion C
    infer_instance
  let : GeometricallyIntegral A.hom := hb.symm ▸ LineBundles.Smooth.IntegralGeometricFibers.BundleCycles.projectiveComponent_geometricallyIntegral X C
  let B : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (show Y.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from Y.structureMap)
  let : AlgebraicGeometry.IsNoetherian B.left := inferInstanceAs (AlgebraicGeometry.IsNoetherian Y.carrier)
  let : LocallyOfFiniteType B.hom := inferInstanceAs (LocallyOfFiniteType Y.structureMap)
  have H := ProductFiberSupportDimension.BundleCycles.productFiberSupport_dimension A B (irreducibleSetEquivPoints.symm y)
  rw [Integral.PulledSupport.BundleCycles.integralPulledSupport_eq_pointClosure, irreducibleSetEquivPoints.apply_symm_apply] at H
  have hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety C).structureMap :=
    congrArg (fun g : (X.componentVariety C).carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g) hb
  exact H.trans (congrArg (fun n => n + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) Y.structureMap) hd)

theorem graphProjectionComponentPoint_dimension (C : irreducibleComponents X.carrier) (y : Y.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension
        (irreducibleSetEquivPoints.symm (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C
          (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (ProjectionComponents.BundleCycles.graphProjectionComponentMap f C) y)))
        (Chow.BundleCycles.graphAmbientStructureMap f) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety C).structureMap +
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) Y.structureMap := by
  rw [ImmersionDimension.BundleCycles.pointClosure_dimension_immersion (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C)]
  have he : ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C ≫ Chow.BundleCycles.graphAmbientStructureMap f =
      ProjectionComponents.BundleCycles.graphProjectionComponentMap f C ≫ Y.structureMap := by
    change ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C ≫ (OpenAmbient.BundleCycles.graphSecondProjection f ≫ Y.structureMap) = _
    rw [← Category.assoc, ProjectionComponents.BundleCycles.graphProjectionComponent_over]
  rw [he]
  exact graphProjectionComponentFiberGeneric_dimension f C y

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionPointDimension.BundleCycles
