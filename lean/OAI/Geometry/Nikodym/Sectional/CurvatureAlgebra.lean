import OAI.Geometry.Nikodym.ChristoffelDerivative

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (g : SmoothCoordinateMetric E)

theorem curvature_add_first {x : E} (hx : x ∈ g.domain) (u v w z : E) :
    g.curvature x (u+v) w z = g.curvature x u w z + g.curvature x v w z := by
  simp only [SmoothCoordinateMetric.curvature, ← g.fderiv_christoffel_apply hx]
  simp only [map_add,add_apply,
    g.christoffel_add_left,g.christoffel_add_right]
  abel

theorem curvature_add_second {x : E} (hx : x ∈ g.domain) (u v w z : E) :
    g.curvature x u (v+w) z = g.curvature x u v z + g.curvature x u w z := by
  simp only [SmoothCoordinateMetric.curvature, ← g.fderiv_christoffel_apply hx]
  simp only [map_add,add_apply,
    g.christoffel_add_left,g.christoffel_add_right]
  abel

theorem curvature_add_third {x : E} (hx : x ∈ g.domain) (u v w z : E) :
    g.curvature x u v (w+z) = g.curvature x u v w + g.curvature x u v z := by
  simp only [SmoothCoordinateMetric.curvature, ← g.fderiv_christoffel_apply hx]
  simp only [map_add,g.christoffel_add_right]
  abel

theorem curvature_smul_first {x : E} (hx : x ∈ g.domain) (a : ℝ) (u v w : E) :
    g.curvature x (a • u) v w = a • g.curvature x u v w := by
  simp only [SmoothCoordinateMetric.curvature, ← g.fderiv_christoffel_apply hx]
  simp only [map_smul,smul_apply,
    g.christoffel_smul_left,g.christoffel_smul_right,smul_add,smul_sub]

theorem curvature_smul_second {x : E} (hx : x ∈ g.domain) (a : ℝ) (u v w : E) :
    g.curvature x u (a • v) w = a • g.curvature x u v w := by
  simp only [SmoothCoordinateMetric.curvature, ← g.fderiv_christoffel_apply hx]
  simp only [map_smul,smul_apply,
    g.christoffel_smul_left,g.christoffel_smul_right,smul_add,smul_sub]

theorem curvature_smul_third {x : E} (hx : x ∈ g.domain) (a : ℝ) (u v w : E) :
    g.curvature x u v (a • w) = a • g.curvature x u v w := by
  simp only [SmoothCoordinateMetric.curvature, ← g.fderiv_christoffel_apply hx]
  simp only [map_smul,g.christoffel_smul_right,smul_add,smul_sub]

/-- First Bianchi follows from symmetry of the constructed connection and
the derivative of that symmetry. -/
theorem curvature_bianchi {x : E} (hx : x ∈ g.domain) (u v w : E) :
    g.curvature x u v w + g.curvature x v w u + g.curvature x w u v = 0 := by
  simp only [SmoothCoordinateMetric.curvature]
  rw [g.fderiv_christoffel_symmetric hx v w u,
    g.fderiv_christoffel_symmetric hx w v u,
    g.fderiv_christoffel_symmetric hx u w v]
  rw [g.christoffel_symmetric hx w u,g.christoffel_symmetric hx v u,
    g.christoffel_symmetric hx w v]
  abel

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
