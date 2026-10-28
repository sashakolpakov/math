import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.InverseChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionChowFamily
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ChowPointSpecialization

/-! # Chow Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ChowPullback.BundleCycles

noncomputable section

/-! The graph construction on the actual codimension Chow quotient:
project the cycle, specialize along the graph, invert normal extension,
and take the indicated codimension component. The full graph equation and
Betti compatibility are separate properties of this constructed map. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)

def graphCyclePullback : Y.RationalDimensionCycle p →ₗ[ℚ] Chow.BundleCycles.ChowQ X p :=
  (GraphNormal.InverseChow.BundleCycles.graphNormalInverseChow f p).comp ((Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker).comp
    ((Chow.BundleCycles.graphProjectionPointPullback f).comp (Chow.BundleCycles.projectiveCyclePointMap Y p)))

theorem graphCyclePullback_relations : Chow.BundleCycles.rationalEquivalenceQ Y p ≤ LinearMap.ker (graphCyclePullback f p) := by
  intro z hz
  change GraphNormal.InverseChow.BundleCycles.graphNormalInverseChow f p (Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker
    (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.projectiveCyclePointMap Y p z))) = 0
  apply GraphNormal.InverseChow.BundleCycles.graphNormalInverseChow_eq_zero_of_all_dimensions
  intro d
  have hp := ProjectionChowFamily.BundleCycles.graphProjectionPointChow_relations f p d hz
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphAmbientStructureMap f) d
    (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.projectiveCyclePointMap Y p z)) = 0 at hp
  have H := congrArg (Global.ChowSpecialization.BundleCycles.globalChowSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphAmbientStructureMap f) d) hp
  rw [Global.ChowPointSpecialization.BundleCycles.globalChowSpecialization_pointClass, map_zero] at H
  exact H

def graphChowPullback : Chow.BundleCycles.ChowQ Y p ⟶ Chow.BundleCycles.ChowQ X p :=
  ModuleCat.ofHom ((Chow.BundleCycles.rationalEquivalenceQ Y p).liftQ (graphCyclePullback f p) (graphCyclePullback_relations f p))

theorem graphChowPullback_cycle (z : Y.RationalDimensionCycle p) :
    graphChowPullback f p (Chow.BundleCycles.cycleToChowQ Y p z) = GraphNormal.InverseChow.BundleCycles.graphNormalInverseChow f p
      (Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.pointCycle Y p z))) := by
  change GraphNormal.InverseChow.BundleCycles.graphNormalInverseChow f p (Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker
    (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.projectiveCyclePointMap Y p z))) = _
  rw [Chow.BundleCycles.projectiveCyclePointMap_apply]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ChowPullback.BundleCycles
