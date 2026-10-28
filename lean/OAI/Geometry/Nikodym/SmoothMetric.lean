import OAI.Geometry.Nikodym.MetricConnection

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A smooth positive coordinate metric on an open set. No connection,
geodesic chart, or curvature-normalization conclusion is included. -/
structure SmoothCoordinateMetric (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  domain : Set E
  isOpen_domain : IsOpen domain
  coefficient : E → E →L[ℝ] E
  smooth : ContDiffOn ℝ ∞ coefficient domain
  symmetric : ∀ x ∈ domain, ∀ u v, ⟪coefficient x u,v⟫ = ⟪u,coefficient x v⟫
  positive : ∀ x ∈ domain, ∀ u, u ≠ 0 → 0 < ⟪coefficient x u,u⟫

namespace SmoothCoordinateMetric

variable (g : SmoothCoordinateMetric E)

theorem invertible {x : E} (hx : x ∈ g.domain) : (g.coefficient x).IsInvertible := by
  have hi : Function.Injective (g.coefficient x) := by
    intro u v huv
    apply sub_eq_zero.mp
    by_contra hne
    have hp := g.positive x hx (u-v) hne
    simp only [map_sub,huv,sub_self,inner_zero_left] at hp
    exact lt_irrefl _ hp
  have hs : Function.Surjective (g.coefficient x) :=
    (LinearMap.injective_iff_surjective).mp hi
  obtain ⟨U,hU⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hi,hs⟩
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ E U,hU⟩

omit [FiniteDimensional ℝ E] in
theorem derivative_symmetric {x : E} (hx : x ∈ g.domain) :
    ∀ w u v, ⟪fderiv ℝ g.coefficient x w u,v⟫ = ⟪u,fderiv ℝ g.coefficient x w v⟫ := by
  apply fderiv_metric_symmetric
  · exact ((g.smooth x hx).contDiffAt (g.isOpen_domain.mem_nhds hx)).differentiableAt (by norm_num)
  · filter_upwards [g.isOpen_domain.mem_nhds hx] with y hy
    exact g.symmetric y hy

def inner (x u v : E) : ℝ := ⟪g.coefficient x u,v⟫

def christoffel (x u v : E) : E := metricChristoffel g.coefficient x u v

theorem coefficient_christoffel {x : E} (hx : x ∈ g.domain) (u v : E) :
    g.coefficient x (g.christoffel x u v) = metricKoszulVector (fderiv ℝ g.coefficient x) u v :=
  (g.invertible hx).self_apply_inverse _

theorem christoffel_symmetric {x : E} (hx : x ∈ g.domain) (u v : E) :
    g.christoffel x u v = g.christoffel x v u := by
  unfold SmoothCoordinateMetric.christoffel metricChristoffel
  rw [metricKoszulVector_symmetric _ (g.derivative_symmetric hx)]

/-- The constructed connection satisfies the actual coordinate Koszul formula. -/
theorem christoffel_koszul {x : E} (hx : x ∈ g.domain) (u v w : E) :
    g.inner x (g.christoffel x u v) w =
      (⟪fderiv ℝ g.coefficient x u v,w⟫ + ⟪fderiv ℝ g.coefficient x v u,w⟫ -
        ⟪fderiv ℝ g.coefficient x w u,v⟫)/2 := by
  unfold SmoothCoordinateMetric.inner
  rw [g.coefficient_christoffel hx,inner_metricKoszulVector]

/-- Metric compatibility is derived from the coefficient field. -/
theorem christoffel_compatible {x : E} (hx : x ∈ g.domain) (u v w : E) :
    g.inner x (g.christoffel x u v) w + g.inner x v (g.christoffel x u w) =
      ⟪fderiv ℝ g.coefficient x u v,w⟫ := by
  unfold SmoothCoordinateMetric.inner
  rw [g.symmetric x hx v,g.coefficient_christoffel hx,g.coefficient_christoffel hx]
  exact metricKoszulVector_compatible _ (g.derivative_symmetric hx) u v w

end SmoothCoordinateMetric
end OAI.Geometry.Nikodym
