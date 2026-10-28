import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponentPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.ClopenFiberCyclePullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.FiberReduced

/-! # Projection Component Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponentCycle.BundleCycles

noncomputable section

/-! The full projection cycle is the finite sum of its actual integral
fiber components. Smoothness makes each generic local length equal to one. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

theorem graphProjectionPointPullback_single (v : Y.carrier) (a : ℚ) :
    Chow.BundleCycles.graphProjectionPointPullback f (Finsupp.single v a) =
      ∑ C ∈ (Set.univ : Set (irreducibleComponents X.carrier)).toFinite.toFinset,
        Finsupp.single (ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint f C v) a := by
  classical
  let := Fintype.ofFinite (irreducibleComponents X.carrier)
  let : ∀ C, GeometricallyIntegral (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C ≫ OpenAmbient.BundleCycles.graphSecondProjection f) :=
    fun C => (ProjectionComponents.BundleCycles.graphProjectionComponent_over f C).symm ▸ inferInstance
  let : ∀ y, IsReduced ((OpenAmbient.BundleCycles.graphSecondProjection f).fiber y) := fun y => Smooth.FiberReduced.BundleCycles.smoothFiber_isReduced _ y
  change FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback (OpenAmbient.BundleCycles.graphSecondProjection f) (Finsupp.single v a) = _
  rw [FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback_single,
    ClopenFiberCyclePullback.BundleCycles.clopenFiber_fundamentalPointCycle (OpenAmbient.BundleCycles.graphSecondProjection f) (ProjectionComponents.BundleCycles.graphProjectionComponent f)
      (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f) (ProjectionComponents.BundleCycles.graphProjectionComponents_cover f), Finset.smul_sum]
  have hu : (Set.univ : Set (irreducibleComponents X.carrier)).toFinite.toFinset = Finset.univ := by
    ext C
    simp only [Set.Finite.mem_toFinset, Set.mem_univ, Finset.mem_univ]
  rw [hu]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finsupp.smul_single, smul_eq_mul, mul_one,
    Integral.FiberCongr.BundleCycles.integralFiberGenericPoint_congr _ (ProjectionComponents.BundleCycles.graphProjectionComponentMap f C) (ProjectionComponents.BundleCycles.graphProjectionComponent_over f C)]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponentCycle.BundleCycles
