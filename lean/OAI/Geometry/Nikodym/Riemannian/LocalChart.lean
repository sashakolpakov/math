import OAI.Geometry.Nikodym.Riemannian.Coordinates
import OAI.Geometry.Nikodym.Riemannian.Restriction
import OAI.Geometry.Nikodym.Riemannian.Uniform

noncomputable section
open Set Metric

namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every smooth positive coordinate metric has a relatively compact
ball on which the actual intrinsic geometry and the Euclidean geometry
are bi-Lipschitz. No metric-comparison hypothesis is imposed. -/
theorem exists_intrinsic_biLipschitz_ball (g : SmoothCoordinateMetric E)
    {x₀ : E} (hx₀ : x₀ ∈ g.domain) :
    ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ 0 < C ∧
      IsCompact (closedBall x₀ r) ∧ closedBall x₀ r ⊆ g.domain ∧
      ∃ hsub : ball x₀ r ⊆ g.domain,
        let g₀ := g.restrict ⟨ball x₀ r,isOpen_ball⟩ hsub
        LipschitzWith ⟨1 / Real.sqrt c,by positivity⟩ (OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g₀) ∧
        LipschitzWith ⟨Real.sqrt C,Real.sqrt_nonneg _⟩ (OAI.Geometry.Nikodym.IntrinsicDomain.ofCoordinate g₀) := by
  obtain ⟨r,c,C,hr,hc,hC,hball,hbounds⟩ := g.locally_uniform_elliptic hx₀
  have hsub : ball x₀ r ⊆ g.domain := ball_subset_closedBall.trans hball
  refine ⟨r,c,C,hr,hc,hC,isCompact_closedBall x₀ r,hball,hsub,?_,?_⟩
  · apply OAI.Geometry.Nikodym.IntrinsicDomain.lipschitz_coordinate _ hc
    intro x hx v
    exact (hbounds x (ball_subset_closedBall hx) v).1
  · apply OAI.Geometry.Nikodym.IntrinsicDomain.lipschitz_ofCoordinate _ (convex_ball x₀ r) hC
    intro x hx v
    exact (hbounds x (ball_subset_closedBall hx) v).2

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
