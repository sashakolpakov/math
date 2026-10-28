import OAI.Geometry.Nikodym.SmoothMetric

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The coordinate transformation law follows algebraically from the metric
identity, its derivative, and symmetry of the second derivative. -/
theorem christoffel_transform_of_metric_derivative
    (g : SmoothCoordinateMetric E) (h : SmoothCoordinateMetric F)
    {x : E} {y : F} (hx : x ∈ g.domain) (hy : y ∈ h.domain)
    (L : E →L[ℝ] F) (hL : Function.Surjective L) (Q : E → E → F)
    (hQ : ∀ u v, Q u v = Q v u)
    (hmetric : ∀ u v, g.inner x u v = h.inner y (L u) (L v))
    (hD : ∀ a u v,
      ⟪fderiv ℝ g.coefficient x a u,v⟫ =
        ⟪fderiv ℝ h.coefficient y (L a) (L u),L v⟫ +
        h.inner y (Q a u) (L v) + h.inner y (L u) (Q a v))
    (u v : E) :
    L (g.christoffel x u v) = Q u v + h.christoffel y (L u) (L v) := by
  have hs : ∀ a b, h.inner y a b = h.inner y b a := by
    intro a b
    exact (h.symmetric y hy a b).trans (real_inner_comm _ _)
  have hp : ∀ w, h.inner y (Q u v + h.christoffel y (L u) (L v)) (L w) =
      h.inner y (L (g.christoffel x u v)) (L w) := by
    intro w
    rw [show h.inner y (Q u v + h.christoffel y (L u) (L v)) (L w) =
      h.inner y (Q u v) (L w) + h.inner y (h.christoffel y (L u) (L v)) (L w) by
        simp only [SmoothCoordinateMetric.inner,map_add,inner_add_left], h.christoffel_koszul hy, ← hmetric]
    rw [g.christoffel_koszul hx, hD u v w, hD v u w, hD w u v]
    rw [hQ v u, hQ w u, hQ w v, hs (L v) (Q u w), hs (L u) (Q v w)]
    ring
  let d := L (g.christoffel x u v) - (Q u v + h.christoffel y (L u) (L v))
  have hz : h.inner y d d = 0 := by
    obtain ⟨w,hw⟩ := hL d
    have he := hp w
    rw [hw] at he
    change h.inner y (L (g.christoffel x u v) -
      (Q u v + h.christoffel y (L u) (L v))) d = 0
    simpa only [SmoothCoordinateMetric.inner,map_sub,inner_sub_left,sub_eq_zero] using he.symm
  have hd : d = 0 := by
    by_contra hn
    exact (ne_of_gt (h.positive y hy d hn)) hz
  exact sub_eq_zero.mp hd

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
