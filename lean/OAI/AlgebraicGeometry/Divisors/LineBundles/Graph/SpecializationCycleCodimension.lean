import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationPointCodimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponentCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Chow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleSet

/-! # Specialization Cycle Codimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationCycleCodimension.BundleCycles

noncomputable section

/-! Specialization of the full graph-projection cycle is supported in
the prescribed codimension, with every fiber component retained. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)

def graphConeCodimensionPart :
    (Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker →₀ ℚ) →ₗ[ℚ] (Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker →₀ ℚ) :=
  Point.CycleSet.BundleCycles.pointCycleSetPart {y | SpecializationPointCodimension.BundleCycles.GraphConePointHasCodimension f p y}

theorem graphProjectionSpecialization_cycle_off_codimension (z : Y.RationalDimensionCycle p)
    (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker) (hy : ¬ SpecializationPointCodimension.BundleCycles.GraphConePointHasCodimension f p y) :
    Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.pointCycle Y p z)) y = 0 := by
  classical
  rw [← Chow.BundleCycles.projectiveCyclePointMap_apply]
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw, add_zero]
  | single Z a =>
    change Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker
      (Chow.BundleCycles.graphProjectionPointPullback f (Finsupp.mapDomain (Chow.BundleCycles.cyclePointEmbedding Y p) (Finsupp.single Z a))) y = 0
    rw [Finsupp.mapDomain_single, ProjectionComponentCycle.BundleCycles.graphProjectionPointPullback_single, map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro C _
    rw [Global.CycleSpecialization.BundleCycles.globalCycleSpecialization_single, Finsupp.smul_apply]
    have hz : Global.CycleSpecialization.BundleCycles.globalPrimeSpecializationQ (OpenAmbient.BundleCycles.graph f).ker
        (ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint f C (Chow.BundleCycles.cyclePointEmbedding Y p Z)) y = 0 := by
      by_contra hn
      have H := SpecializationPointCodimension.BundleCycles.graphProjectionSpecialization_point_codimension f C (Chow.BundleCycles.cyclePointEmbedding Y p Z) y hn
      have hp : Y.supportCodimension (irreducibleSetEquivPoints.symm (Chow.BundleCycles.cyclePointEmbedding Y p Z)) = p := by
        change Y.supportCodimension (irreducibleSetEquivPoints.symm (irreducibleSetEquivPoints Z.val)) = p
        rw [irreducibleSetEquivPoints.symm_apply_apply]
        exact Z.property
      exact hy (hp ▸ H)
    rw [hz, smul_zero]

theorem graphProjectionSpecialization_cycle_codimension (z : Y.RationalDimensionCycle p) :
    graphConeCodimensionPart f p
      (Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.pointCycle Y p z))) =
      Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.pointCycle Y p z)) := by
  ext y
  by_cases hy : SpecializationPointCodimension.BundleCycles.GraphConePointHasCodimension f p y
  · exact Point.CycleSet.BundleCycles.pointCycleSetPart_apply_mem _ _ y hy
  · exact (Point.CycleSet.BundleCycles.pointCycleSetPart_apply_notMem _ _ y hy).trans
      (graphProjectionSpecialization_cycle_off_codimension f p z y hy).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationCycleCodimension.BundleCycles
