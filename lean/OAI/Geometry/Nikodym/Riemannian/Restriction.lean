import OAI.Geometry.Nikodym.Riemannian.Smooth

noncomputable section
open Set
open scoped ContDiff

namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Restrict a metric to an open subdomain without changing its
coefficient field, connection, or curvature expressions. -/
def restrict (g : SmoothCoordinateMetric E) (U : TopologicalSpace.Opens E)
    (hU : (U : Set E) ⊆ g.domain) : SmoothCoordinateMetric E where
  domain := U
  isOpen_domain := U.isOpen
  coefficient := g.coefficient
  smooth := g.smooth.mono hU
  symmetric x hx := g.symmetric x (hU hx)
  positive x hx := g.positive x (hU hx)

omit [FiniteDimensional ℝ E] in
@[simp] theorem restrict_domain (g : SmoothCoordinateMetric E)
    (U : TopologicalSpace.Opens E) (hU : (U : Set E) ⊆ g.domain) :
    (g.restrict U hU).domain = U := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem restrict_coefficient (g : SmoothCoordinateMetric E)
    (U : TopologicalSpace.Opens E) (hU : (U : Set E) ⊆ g.domain) :
    (g.restrict U hU).coefficient = g.coefficient := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem restrict_inner (g : SmoothCoordinateMetric E)
    (U : TopologicalSpace.Opens E) (hU : (U : Set E) ⊆ g.domain) (x u v : E) :
    (g.restrict U hU).inner x u v = g.inner x u v := rfl

@[simp] theorem restrict_christoffel (g : SmoothCoordinateMetric E)
    (U : TopologicalSpace.Opens E) (hU : (U : Set E) ⊆ g.domain) (x u v : E) :
    (g.restrict U hU).christoffel x u v = g.christoffel x u v := rfl

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
