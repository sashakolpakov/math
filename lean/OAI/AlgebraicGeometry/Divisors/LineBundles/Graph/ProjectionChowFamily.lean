import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponents
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.ClopenPrincipalRelations
import OAI.AlgebraicGeometry.Divisors.LineBundles.Chow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.MapCharacterization

/-! # Projection Chow Family -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionChowFamily.BundleCycles

noncomputable section

/-! The actual graph projection descends its full fiber-cycle formula to
the Chow quotient in every dimension grade, retaining all source components. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)

theorem graphProjectionPointChow_relations (d : ℕ) : Chow.BundleCycles.rationalEquivalenceQ Y p ≤
    LinearMap.ker ((Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphAmbientStructureMap f) d).comp
      ((Chow.BundleCycles.graphProjectionPointPullback f).comp (Chow.BundleCycles.projectiveCyclePointMap Y p))) := by
  classical
  let := Fintype.ofFinite (irreducibleComponents X.carrier)
  let : ∀ C, GeometricallyIntegral (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C ≫ OpenAmbient.BundleCycles.graphSecondProjection f) :=
    fun C => (ProjectionComponents.BundleCycles.graphProjectionComponent_over f C).symm ▸ inferInstance
  apply Submodule.span_le.mpr
  rintro z ⟨W, hW, g, hg, hz⟩
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphAmbientStructureMap f) d
    (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.projectiveCyclePointMap Y p z)) = 0
  rw [Chow.BundleCycles.projectiveCyclePointMap_apply, hz]
  exact Smooth.ClopenPrincipalRelations.BundleCycles.smoothClopenFiberCycle_principal_zero (OpenAmbient.BundleCycles.graphSecondProjection f) (Chow.BundleCycles.graphAmbientStructureMap f)
    (ProjectionComponents.BundleCycles.graphProjectionComponent f) (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f)
    (ProjectionComponents.BundleCycles.graphProjectionComponents_cover f) d W g hg

def graphProjectionChowFamily : Geometric.MapCharacterization.BundleCycles.GraphProjectionChowFamily f p := fun d =>
  (Chow.BundleCycles.rationalEquivalenceQ Y p).liftQ ((Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphAmbientStructureMap f) d).comp
    ((Chow.BundleCycles.graphProjectionPointPullback f).comp (Chow.BundleCycles.projectiveCyclePointMap Y p))) (graphProjectionPointChow_relations f p d)

theorem graphProjectionChowFamily_cycle (d : ℕ) (z : Y.RationalDimensionCycle p) :
    graphProjectionChowFamily f p d (Chow.BundleCycles.cycleToChowQ Y p z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphAmbientStructureMap f) d (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.pointCycle Y p z)) := by
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphAmbientStructureMap f) d
    (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.projectiveCyclePointMap Y p z)) = _
  rw [Chow.BundleCycles.projectiveCyclePointMap_apply]

theorem graphProjectionChowFamily_isGeometric :
    Geometric.MapCharacterization.BundleCycles.IsGraphProjectionChowFamily f p (graphProjectionChowFamily f p) :=
  graphProjectionChowFamily_cycle f p

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionChowFamily.BundleCycles
