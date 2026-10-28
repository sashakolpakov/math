import OAI.Geometry.Nikodym.SmoothMetric

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Uniqueness of a torsion-free metric-compatible connection, proved
directly from the coordinate Koszul formula. -/
theorem christoffel_eq_of_symmetric_compatible (g : SmoothCoordinateMetric E)
    {x : E} (hx : x ∈ g.domain) (Γ : E → E → E)
    (hsym : ∀ u v, Γ u v = Γ v u)
    (hcompat : ∀ u v w, g.inner x (Γ u v) w + g.inner x v (Γ u w) =
      ⟪fderiv ℝ g.coefficient x u v,w⟫) (u v : E) :
    g.christoffel x u v = Γ u v := by
  have hs : ∀ a b, g.inner x a b = g.inner x b a := by
    intro a b
    exact (g.symmetric x hx a b).trans (real_inner_comm _ _)
  have he : ∀ w, g.inner x (g.christoffel x u v) w = g.inner x (Γ u v) w := by
    intro w
    rw [g.christoffel_koszul hx, ← hcompat u v w, ← hcompat v u w, ← hcompat w u v]
    rw [hsym v u, hsym w u, hsym w v, hs v (Γ u w), hs u (Γ v w)]
    ring
  let d := g.christoffel x u v - Γ u v
  have hz : g.inner x d d = 0 := by
    simpa only [d,SmoothCoordinateMetric.inner,map_sub,inner_sub_left,sub_eq_zero] using he d
  have hd : d = 0 := by
    by_contra hn
    exact (ne_of_gt (g.positive x hx d hn)) hz
  exact sub_eq_zero.mp hd

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
