import OAI.Geometry.Nikodym.Riemannian.Coordinates

noncomputable section
open Set Bundle Manifold
open scoped ENNReal

namespace OAI.Geometry.Nikodym.IntrinsicDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem edist_ne_top_of_convex (g : SmoothCoordinateMetric E)
    (hconv : Convex ℝ g.domain) {C : ℝ} (hC : 0 < C)
    (hupper : ∀ x ∈ g.domain, ∀ v, g.inner x v v ≤ C * ‖v‖^2)
    (x y : IntrinsicDomain g) : edist x y ≠ ⊤ := by
  rw [IntrinsicDomain.edist_eq]
  have h := g.riemannianEDist_le_of_convex hconv hC hupper x y
  exact (lt_of_le_of_lt h (by finiteness)).ne

/-- On a convex uniformly bounded coordinate domain, the canonical
finite metric induced by Riemannian path length. This preserves the
already constructed intrinsic `edist` and topology. -/
@[instance_reducible]
def metricSpaceOfConvex (g : SmoothCoordinateMetric E)
    (hconv : Convex ℝ g.domain) {C : ℝ} (hC : 0 < C)
    (hupper : ∀ x ∈ g.domain, ∀ v, g.inner x v v ≤ C * ‖v‖^2) :
    MetricSpace (IntrinsicDomain g) :=
  EMetricSpace.toMetricSpace (IntrinsicDomain.edist_ne_top_of_convex g hconv hC hupper)

end OAI.Geometry.Nikodym.IntrinsicDomain
