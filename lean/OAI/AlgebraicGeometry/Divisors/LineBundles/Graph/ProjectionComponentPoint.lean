import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponents
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberCongr

/-! # Projection Component Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponentPoint.BundleCycles

noncomputable section

/-! The actual generic point in each graph-projection fiber component,
with its first-component membership and exact second projection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphProjectionComponentPoint (C : irreducibleComponents X.carrier) (y : Y.carrier) : OpenAmbient.BundleCycles.graphAmbient f :=
  ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (ProjectionComponents.BundleCycles.graphProjectionComponentMap f C) y)

theorem graphProjectionComponentInclusion_first_mem (C : irreducibleComponents X.carrier)
    (a : ProjectionComponents.BundleCycles.graphProjectionComponent f C) :
    OpenAmbient.BundleCycles.graphFirstProjection f (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C a) ∈ Set.range (X.componentInclusion C) := by
  let : ∀ D, IsOpenImmersion (X.componentInclusion D) := fun D => X.componentInclusion_isOpenImmersion D
  let : ∀ D, IsClosedImmersion (X.componentInclusion D) := fun D => X.componentInclusion_isClosedImmersion D
  have H : Set.range (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C) =
      OpenAmbient.BundleCycles.graphFirstProjection f ⁻¹' Set.range (X.componentInclusion C) :=
    ClopenCoverBaseChange.BundleCycles.clopenCoverBaseChangeMap_range (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap)
      (fun D => (X.componentVariety D).carrier) X.componentInclusion Y.structureMap C
  change ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C a ∈ OpenAmbient.BundleCycles.graphFirstProjection f ⁻¹' Set.range (X.componentInclusion C)
  rw [← H]
  exact ⟨a, rfl⟩

theorem graphProjectionComponentPoint_first_mem (C : irreducibleComponents X.carrier) (y : Y.carrier) :
    OpenAmbient.BundleCycles.graphFirstProjection f (graphProjectionComponentPoint f C y) ∈ Set.range (X.componentInclusion C) :=
  graphProjectionComponentInclusion_first_mem f C _

theorem graphProjectionComponentPoint_second (C : irreducibleComponents X.carrier) (y : Y.carrier) :
    OpenAmbient.BundleCycles.graphSecondProjection f (graphProjectionComponentPoint f C y) = y :=
  (congrArg (fun a => a (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (ProjectionComponents.BundleCycles.graphProjectionComponentMap f C) y))
    (ProjectionComponents.BundleCycles.graphProjectionComponent_over f C)).trans
      (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection (ProjectionComponents.BundleCycles.graphProjectionComponentMap f C) y)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponentPoint.BundleCycles
